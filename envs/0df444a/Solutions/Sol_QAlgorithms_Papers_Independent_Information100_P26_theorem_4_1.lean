-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P26.theorem_4_1
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T12:44:30.402297+00:00
-- url     : https://prove2.me/submissions/7847e443-96be-41de-a46e-8461ca1886b2

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P26
import Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P26_lemma_4_3
import Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P26_lemma_4_5


noncomputable section

open scoped BigOperators ComplexConjugate Matrix ComplexOrder Matrix.Norms.Frobenius

open MeasureTheory Filter Set

namespace QAlgorithms.Papers.Independent.Information100.P26

attribute [local instance] Classical.propDecidable Classical.decEq

attribute [local instance] QAlgorithms.Papers.Independent.Information100.P26.unitaryMeasurable

namespace X8HA

variable {d : ℕ}

instance borelU : BorelSpace (Unitary d) := ⟨rfl⟩

instance cenM : ContinuousENorm (Map d) := SeminormedAddGroup.toContinuousENorm

instance pmM : TopologicalSpace.PseudoMetrizableSpace (Map d) :=
  PseudoEMetricSpace.pseudoMetrizableSpace

instance scM : SecondCountableTopology (Map d) :=
  inferInstanceAs (SecondCountableTopology (Fin d × Fin d → Fin d × Fin d → ℂ))

lemma unit_cpt : IsCompact (Matrix.unitaryGroup (Fin d) ℂ : Set (Mat d)) := by
  have hS : IsCompact (Set.pi Set.univ fun _ : Fin d =>
      Set.pi Set.univ fun _ : Fin d => Metric.closedBall (0 : ℂ) 1) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
  have hC : IsClosed (Matrix.unitaryGroup (Fin d) ℂ : Set (Mat d)) := by
    have : (Matrix.unitaryGroup (Fin d) ℂ : Set (Mat d)) =
        {U | star U * U = 1} ∩ {U | U * star U = 1} := by
      ext U; exact Unitary.mem_iff
    rw [this]
    exact (isClosed_eq (continuous_id.matrix_conjTranspose.matrix_mul continuous_id)
      continuous_const).inter
      (isClosed_eq (continuous_id.matrix_mul continuous_id.matrix_conjTranspose) continuous_const)
  refine hS.of_isClosed_subset hC ?_
  intro U hU
  simp only [Set.mem_pi, Set.mem_univ, Metric.mem_closedBall, dist_zero_right, forall_true_left]
  intro i j
  exact entry_norm_bound_of_unitary hU i j

instance cptU : CompactSpace (Unitary d) := isCompact_iff_compactSpace.mp unit_cpt

lemma integ {f : Unitary d → Map d} (hf : Continuous f) (mu : Measure (Unitary d))
    [IsFiniteMeasure mu] : Integrable f mu :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

/-- integral commutes with ℝ-linear maps -/
lemma int_lin {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E] (L : Map d →ₗ[ℝ] E) {f : Unitary d → Map d} (mu : Measure (Unitary d))
    (hf : Integrable f mu) : ∫ V, L (f V) ∂mu = L (∫ V, f V ∂mu) := by
  have := ContinuousLinearMap.integral_comp_comm (LinearMap.toContinuousLinearMap L) hf
  exact this

def ev (p q : Fin d × Fin d) : Map d →ₗ[ℝ] ℂ where
  toFun M := M p q
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma int_ent {f : Unitary d → Map d} (mu : Measure (Unitary d))
    (hf : Integrable f mu) (p q : Fin d × Fin d) : (∫ V, f V ∂mu) p q = ∫ V, f V p q ∂mu :=
  (int_lin (ev p q) mu hf).symm

def lmul (A : Map d) : Map d →ₗ[ℝ] Map d where
  toFun M := A * M
  map_add' _ _ := Matrix.mul_add _ _ _
  map_smul' _ _ := Matrix.mul_smul _ _ _

def rmul (A : Map d) : Map d →ₗ[ℝ] Map d where
  toFun M := M * A
  map_add' _ _ := Matrix.add_mul _ _ _
  map_smul' _ _ := Matrix.smul_mul _ _ _

lemma int_lmul {f : Unitary d → Map d} (mu : Measure (Unitary d))
    (hf : Integrable f mu) (A : Map d) : ∫ V, A * f V ∂mu = A * ∫ V, f V ∂mu :=
  int_lin (lmul A) mu hf

lemma int_rmul {f : Unitary d → Map d} (mu : Measure (Unitary d))
    (hf : Integrable f mu) (A : Map d) : ∫ V, f V * A ∂mu = (∫ V, f V ∂mu) * A :=
  int_lin (rmul A) mu hf

lemma cont_coe : Continuous (fun V : Unitary d => (V : Mat d)) := continuous_subtype_val

lemma cont_ad {g : Unitary d → Mat d} (hg : Continuous g) :
    Continuous (fun V => ad (g V)) := by
  unfold ad
  refine continuous_pi fun p => continuous_pi fun q => ?_
  exact ((hg.matrix_elem _ _).mul (Complex.continuous_conj.comp (hg.matrix_elem _ _)))

lemma cont_ad_coe : Continuous (fun V : Unitary d => ad (V : Mat d)) := cont_ad cont_coe

lemma cont_ad_star : Continuous (fun V : Unitary d => ad (V : Mat d)ᴴ) :=
  cont_ad cont_coe.matrix_conjTranspose

/-- left invariance -/
lemma int_left (mu : Measure (Unitary d))
    (hmu : ∀ U : Unitary d, Measure.map (fun V => U * V) mu = mu)
    {f : Unitary d → Map d} (hf : Continuous f) (W : Unitary d) :
    ∫ V, f (W * V) ∂mu = ∫ V, f V ∂mu := by
  have hm : Measurable (fun V : Unitary d => W * V) := (continuous_const_mul W).measurable
  conv_rhs => rw [← hmu W]
  rw [integral_map hm.aemeasurable hf.aestronglyMeasurable]

end X8HA

end QAlgorithms.Papers.Independent.Information100.P26


noncomputable section

open scoped BigOperators ComplexConjugate Matrix ComplexOrder Matrix.Norms.Frobenius

open MeasureTheory Filter Set

namespace QAlgorithms.Papers.Independent.Information100.P26

attribute [local instance] Classical.propDecidable Classical.decEq

attribute [local instance] QAlgorithms.Papers.Independent.Information100.P26.unitaryMeasurable

namespace X8HA

variable {d : ℕ}

lemma cont_adX {X : Type*} [TopologicalSpace X] {g : X → Mat d} (hg : Continuous g) :
    Continuous (fun x => ad (g x)) := by
  unfold ad
  refine continuous_pi fun p => continuous_pi fun q => ?_
  exact ((hg.matrix_elem _ _).mul (Complex.continuous_conj.comp (hg.matrix_elem _ _)))

lemma cont_beta : Continuous (fun z : Unitary d × Unitary d => beta z.1 z.2) := by
  unfold beta
  exact ((cont_adX (cont_coe.comp continuous_fst)).matrix_mul continuous_const).matrix_mul
    (cont_adX (cont_coe.comp continuous_snd).matrix_conjTranspose)

instance scMat : SecondCountableTopology (Mat d) :=
  inferInstanceAs (SecondCountableTopology (Fin d → Fin d → ℂ))

instance scU : SecondCountableTopology (Unitary d) :=
  TopologicalSpace.Subtype.secondCountableTopology _

lemma cont_w (t : Map d) :
    Continuous (fun z : Unitary d × Unitary d => (hsInner (beta z.1 z.2) t).re) := by
  unfold hsInner
  refine Complex.continuous_re.comp (continuous_finsetSum _ fun p _ =>
    continuous_finsetSum _ fun q _ => ?_)
  exact (Complex.continuous_conj.comp (cont_beta.matrix_elem p q)).mul continuous_const

lemma par_cont (mu : Measure (Unitary d)) [IsFiniteMeasure mu]
    {f : Unitary d → Unitary d → Map d} (hf : Continuous (Function.uncurry f)) :
    Continuous (fun U => ∫ V, f U V ∂mu) := by
  have := continuous_parametric_integral_of_continuous (μ := mu) hf isCompact_univ
  rw [Measure.restrict_univ] at this
  exact this

lemma wlin (mu : Measure (Unitary d)) [IsFiniteMeasure mu]
    {w : Unitary d → Unitary d → ℝ} (hw : Continuous (Function.uncurry w)) (c e : ℝ) :
    weightedIntegral mu (fun U V => c * w U V + e) =
      c • weightedIntegral mu w + e • weightedIntegral mu (fun _ _ => 1) := by
  unfold weightedIntegral
  have hf : Continuous (Function.uncurry fun U V => w U V • beta U V) := by
    exact hw.smul cont_beta
  have hg : Continuous (Function.uncurry fun U V => (1 : ℝ) • beta (d := d) U V) := by
    simpa [Function.uncurry_def] using cont_beta
  have e1 : ∀ U V, (c * w U V + e) • beta U V = c • (w U V • beta U V) + e • ((1 : ℝ) • beta U V) := by
    intro U V; rw [add_smul, mul_smul, one_smul]
  simp only [e1]
  have inner : ∀ U, ∫ V, c • (w U V • beta U V) + e • ((1 : ℝ) • beta U V) ∂mu =
      c • ∫ V, w U V • beta U V ∂mu + e • ∫ V, (1 : ℝ) • beta U V ∂mu := by
    intro U
    have i1 : Integrable (fun V => w U V • beta U V) mu :=
      integ (hf.comp (Continuous.prodMk_right U)) mu
    have i2 : Integrable (fun V => (1 : ℝ) • beta U V) mu :=
      integ (hg.comp (Continuous.prodMk_right U)) mu
    have i1' : Integrable (fun V => c • (w U V • beta U V)) mu := i1.smul c
    have i2' : Integrable (fun V => e • ((1 : ℝ) • beta U V)) mu := i2.smul e
    rw [integral_add i1' i2', integral_smul, integral_smul]
  simp only [inner]
  have o1 := integ (par_cont mu hf) mu
  have o2 := integ (par_cont mu hg) mu
  have o1' : Integrable (fun U => c • ∫ V, w U V • beta U V ∂mu) mu := o1.smul c
  have o2' : Integrable (fun U => e • ∫ V, (1 : ℝ) • beta U V ∂mu) mu := o2.smul e
  rw [integral_add o1' o2', integral_smul, integral_smul]

lemma ad_one_dim (U : Unitary 1) : ad (U : Mat 1) = 1 := by
  have h := congrFun (congrFun (Matrix.mem_unitaryGroup_iff.mp U.2) 0) 0
  rw [Matrix.mul_apply, Fin.sum_univ_one, Matrix.star_apply, Complex.star_def] at h
  ext p q
  rw [Subsingleton.elim p (0, 0), Subsingleton.elim q (0, 0)]
  simpa [ad] using h

lemma beta_one_dim (U V : Unitary 1) : beta U V = 1 := by
  have hV : ((V : Mat 1))ᴴ ∈ Matrix.unitaryGroup (Fin 1) ℂ := by
    rw [← Matrix.star_eq_conjTranspose]; exact Unitary.star_mem V.2
  have h2 : ad ((V : Mat 1))ᴴ = 1 := ad_one_dim ⟨_, hV⟩
  have h3 : dephasing 1 = 1 := by
    ext p q
    rw [Subsingleton.elim p (0, 0), Subsingleton.elim q (0, 0)]
    simp [dephasing]
  rw [beta, ad_one_dim, h2, h3, Matrix.mul_one, Matrix.mul_one]

theorem x8_41 (hd : 0 < d) (mu : Measure (Unitary d))
    (hmu : NormalizedHaar mu) (t : Map d) (ht : UnitalChannel t) :
    t = weightedIntegral mu (fun U V =>
      integralDenominator d * (hsInner (beta U V) t).re - integralDenominator d + 1) := by
  haveI := hmu.1
  rcases (by omega : d = 1 ∨ 2 ≤ d) with h1 | h2
  · subst h1
    have hw : (fun U V : Unitary 1 =>
        integralDenominator 1 * (hsInner (beta U V) t).re - integralDenominator 1 + 1) =
        fun _ _ => 1 := by
      funext U V; simp [integralDenominator]
    rw [hw]
    unfold weightedIntegral
    simp only [beta_one_dim, one_smul]
    rw [integral_const, integral_const]
    simp only [probReal_univ, one_smul]
    have h := congrFun (congrFun ht.2 0) 0
    simp only [applyMap, QAlgorithms.act, Matrix.mulVec, dotProduct] at h
    rw [Fintype.sum_eq_single ((0 : Fin 1), (0 : Fin 1))
      (fun x hx => absurd (Subsingleton.elim x _) hx)] at h
    ext p q
    rw [Subsingleton.elim p (0, 0), Subsingleton.elim q (0, 0)]
    simpa using h
  · have hD : integralDenominator d ≠ 0 := by
      unfold integralDenominator
      have : (2 : ℝ) ≤ d := by exact_mod_cast h2
      have a1 : (0 : ℝ) < (d : ℝ) - 1 := by linarith
      have a2 : (0 : ℝ) < ((d : ℝ) + 1) ^ 2 := by positivity
      exact (mul_pos a1 a2).ne'
    have e : (fun U V => integralDenominator d * (hsInner (beta U V) t).re -
        integralDenominator d + 1) = fun U V => integralDenominator d * (hsInner (beta U V) t).re +
        (1 - integralDenominator d) := by
      funext U V; ring
    rw [e, wlin mu (w := fun U V => (hsInner (beta U V) t).re) (by exact cont_w t),
      lemma_4_5 h2 mu hmu t ht, (lemma_4_3 h2 mu hmu).1]
    rw [smul_add, smul_smul, smul_smul, mul_inv_cancel₀ hD, one_smul, add_assoc, ← add_smul]
    have : integralDenominator d * (1 - (integralDenominator d)⁻¹) + (1 - integralDenominator d) = 0 := by
      field_simp; ring
    rw [this, zero_smul, add_zero]

end X8HA

end QAlgorithms.Papers.Independent.Information100.P26

section

open scoped BigOperators ComplexConjugate Matrix ComplexOrder Matrix.Norms.Frobenius

open MeasureTheory

attribute [local instance] Classical.propDecidable Classical.decEq

attribute [local instance] QAlgorithms.Papers.Independent.Information100.P26.unitaryMeasurable

open QAlgorithms.Papers.Independent.Information100.P26 in
theorem solution {d : ℕ} (hd : 0 < d) (mu : Measure (Unitary d))
    (hmu : NormalizedHaar mu) (t : Map d) (ht : UnitalChannel t) :
    t = weightedIntegral mu (fun U V =>
      integralDenominator d * (hsInner (beta U V) t).re - integralDenominator d + 1) :=
  X8HA.x8_41 hd mu hmu t ht

end
