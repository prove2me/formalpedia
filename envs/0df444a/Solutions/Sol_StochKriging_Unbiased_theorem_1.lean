-- Prove2me | solution 1 for StochKriging.Unbiased.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T02:28:00.007741+00:00
-- url     : https://prove2.me/submissions/64400fd5-864c-4b0a-831f-3ffd502e2a14

import Mathlib
import Definitions.Def_StochKriging_Unbiased_Model
import Definitions.Def_StochKriging_Unbiased_Predictor

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace SKUnbiasedAux

open Matrix

/-- sample mean of a real sequence -/
noncomputable def mean' (y : ℕ → ℝ) (m : ℕ) : ℝ := (1 / (m : ℝ)) * ∑ j ∈ Finset.range m, y j

/-- sample variance of a real sequence -/
noncomputable def var' (y : ℕ → ℝ) (m : ℕ) : ℝ :=
  (1 / ((m : ℝ) - 1)) * ∑ j ∈ Finset.range m, (y j - mean' y m) ^ 2

lemma mean'_shift (a : ℝ) (y : ℕ → ℝ) {m : ℕ} (hm : m ≠ 0) :
    mean' (fun j => a + y j) m = a + mean' y m := by
  unfold mean'
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have : (m : ℝ) ≠ 0 := by exact_mod_cast hm
  field_simp

lemma var'_shift (a : ℝ) (y : ℕ → ℝ) {m : ℕ} (hm : m ≠ 0) :
    var' (fun j => a + y j) m = var' y m := by
  unfold var'
  rw [mean'_shift a y hm]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

lemma mean'_neg (y : ℕ → ℝ) (m : ℕ) : mean' (fun j => -y j) m = -mean' y m := by
  unfold mean'
  rw [Finset.sum_neg_distrib]; ring

lemma var'_neg (y : ℕ → ℝ) (m : ℕ) : var' (fun j => -y j) m = var' y m := by
  unfold var'
  rw [mean'_neg]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

lemma mean'_congr {y y' : ℕ → ℝ} {m : ℕ} (h : ∀ j < m, y j = y' j) : mean' y m = mean' y' m := by
  unfold mean'
  congr 1
  exact Finset.sum_congr rfl fun j hj => h j (Finset.mem_range.1 hj)

lemma var'_congr {y y' : ℕ → ℝ} {m : ℕ} (h : ∀ j < m, y j = y' j) : var' y m = var' y' m := by
  unfold var'
  rw [mean'_congr h]
  congr 1
  exact Finset.sum_congr rfl fun j hj => by rw [h j (Finset.mem_range.1 hj)]

lemma var'_nonneg (y : ℕ → ℝ) {m : ℕ} (hm : 1 ≤ m) : 0 ≤ var' y m := by
  unfold var'
  have : (1 : ℝ) ≤ m := by exact_mod_cast hm
  apply mul_nonneg
  · apply div_nonneg zero_le_one; linarith
  · exact Finset.sum_nonneg fun j _ => sq_nonneg _

/-- coercivity of a positive definite matrix (sup norm) -/
lemma posDef_coercive {k : ℕ} (A : Matrix (Fin k) (Fin k) ℝ) (hA : A.PosDef) :
    ∃ l : ℝ, 0 < l ∧ ∀ v : Fin k → ℝ, l * ‖v‖ ^ 2 ≤ v ⬝ᵥ (A *ᵥ v) := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    refine ⟨1, one_pos, fun v => ?_⟩
    have : v = 0 := Subsingleton.elim _ _
    subst this; simp
  · have hne : (Metric.sphere (0 : Fin k → ℝ) 1).Nonempty := by
      haveI : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
      exact NormedSpace.sphere_nonempty.2 zero_le_one
    have hcont : Continuous fun v : Fin k → ℝ => v ⬝ᵥ (A *ᵥ v) := by
      unfold dotProduct mulVec dotProduct; fun_prop
    obtain ⟨u, hu, hmin⟩ := (isCompact_sphere (0 : Fin k → ℝ) 1).exists_isMinOn hne
      hcont.continuousOn
    have hu0 : u ≠ 0 := by
      intro h; subst h; simp at hu
    have hpos : 0 < u ⬝ᵥ (A *ᵥ u) := by
      simpa using hA.dotProduct_mulVec_pos hu0
    refine ⟨_, hpos, fun v => ?_⟩
    by_cases hv : v = 0
    · subst hv; simp
    · have hvn : 0 < ‖v‖ := norm_pos_iff.2 hv
      set w := ‖v‖⁻¹ • v with hw
      have hws : w ∈ Metric.sphere (0 : Fin k → ℝ) 1 := by
        simp [hw, norm_smul, hvn.ne']
      have h1 := hmin hws
      simp only [Set.mem_setOf_eq] at h1
      have hvw : v = ‖v‖ • w := by
        rw [hw, smul_smul, mul_inv_cancel₀ hvn.ne', one_smul]
      have : v ⬝ᵥ (A *ᵥ v) = ‖v‖ ^ 2 * (w ⬝ᵥ (A *ᵥ w)) := by
        conv_lhs => rw [hvw]
        rw [mulVec_smul, smul_dotProduct, dotProduct_smul]
        simp [smul_eq_mul]; ring
      rw [this]
      nlinarith [sq_nonneg ‖v‖]

/-- uniform bound on `c ᵥ* (A + D)⁻¹` for PD `A` and PSD `D` -/
lemma bound_vecMul_inv {k : ℕ} (A : Matrix (Fin k) (Fin k) ℝ) (hA : A.PosDef) (c : Fin k → ℝ) :
    ∃ C : ℝ, ∀ D : Matrix (Fin k) (Fin k) ℝ, D.PosSemidef →
      ∀ i, |(c ᵥ* (A + D)⁻¹) i| ≤ C := by
  obtain ⟨l, hl, hcoer⟩ := posDef_coercive A hA
  refine ⟨(∑ i, |c i|) / l, fun D hD i => ?_⟩
  have hAD : (A + D).PosDef := hA.add_posSemidef hD
  have hu : IsUnit (A + D).det := (Matrix.isUnit_iff_isUnit_det _).1 hAD.isUnit
  set w := c ᵥ* (A + D)⁻¹ with hw
  have hwc : w ᵥ* (A + D) = c := by
    rw [hw, vecMul_vecMul, nonsing_inv_mul _ hu, vecMul_one]
  have hq : w ⬝ᵥ ((A + D) *ᵥ w) = c ⬝ᵥ w := by
    rw [dotProduct_mulVec, hwc]
  have hD' : 0 ≤ w ⬝ᵥ (D *ᵥ w) := by
    simpa using hD.dotProduct_mulVec_nonneg w
  have hsplit : w ⬝ᵥ ((A + D) *ᵥ w) = w ⬝ᵥ (A *ᵥ w) + w ⬝ᵥ (D *ᵥ w) := by
    rw [add_mulVec, dotProduct_add]
  have hcw : c ⬝ᵥ w ≤ (∑ i, |c i|) * ‖w‖ := by
    unfold dotProduct
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun j _ => ?_
    calc c j * w j ≤ |c j * w j| := le_abs_self _
      _ = |c j| * |w j| := abs_mul _ _
      _ ≤ |c j| * ‖w‖ := by
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        have := norm_le_pi_norm w j
        simpa [Real.norm_eq_abs] using this
  have hmain : l * ‖w‖ ^ 2 ≤ (∑ i, |c i|) * ‖w‖ := by
    have := hcoer w; linarith
  have hwi : |w i| ≤ ‖w‖ := by
    have := norm_le_pi_norm w i
    simpa [Real.norm_eq_abs] using this
  have hwn : ‖w‖ ≤ (∑ i, |c i|) / l := by
    rcases (norm_nonneg w).eq_or_lt with h0 | h0
    · rw [← h0]; exact div_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _) hl.le
    · rw [le_div_iff₀ hl]; nlinarith
  linarith


section Fns
variable {k : ℕ} (N : ℕ)

/-- read off replication `j` at design point `i` from a finite noise vector -/
noncomputable def T (e : Fin k × Fin N → ℝ) (j : ℕ) (i : Fin k) : ℝ :=
  if h : j < N then e (i, ⟨j, h⟩) else 0

variable (n : Fin k → ℕ)

noncomputable def Dg (e : Fin k × Fin N → ℝ) : Matrix (Fin k) (Fin k) ℝ :=
  Matrix.diagonal fun i => var' (fun j => T N e j i) (n i) / (n i : ℝ)

variable (A : Matrix (Fin k) (Fin k) ℝ) (c : Fin k → ℝ)

noncomputable def hfun (e : Fin k × Fin N → ℝ) : Fin k → ℝ := c ᵥ* (A + Dg N n e)⁻¹

noncomputable def Lfun (e : Fin k × Fin N → ℝ) (i : Fin k) : ℝ := mean' (fun j => T N e j i) (n i)

lemma T_neg (e : Fin k × Fin N → ℝ) (j : ℕ) (i : Fin k) :
    T N (fun p => -e p) j i = -T N e j i := by
  unfold T; split_ifs <;> simp

lemma Dg_neg (e : Fin k × Fin N → ℝ) : Dg N n (fun p => -e p) = Dg N n e := by
  unfold Dg
  congr 1; funext i
  simp only [T_neg, var'_neg]

lemma hfun_neg (e : Fin k × Fin N → ℝ) : hfun N n A c (fun p => -e p) = hfun N n A c e := by
  unfold hfun; rw [Dg_neg]

lemma Lfun_neg (e : Fin k × Fin N → ℝ) (i : Fin k) :
    Lfun N n (fun p => -e p) i = -Lfun N n e i := by
  unfold Lfun; simp only [T_neg, mean'_neg]

lemma T_cont (j : ℕ) (i : Fin k) : Continuous fun e : Fin k × Fin N → ℝ => T N e j i := by
  unfold T
  by_cases h : j < N
  · simp only [h, dite_true]; exact continuous_apply _
  · simp only [h, dite_false]; exact continuous_const

lemma Lfun_cont (i : Fin k) : Continuous fun e => Lfun N n e i := by
  unfold Lfun mean'
  exact continuous_const.mul (continuous_finset_sum _ fun j _ => T_cont N j i)

lemma Dg_cont : Continuous fun e => Dg N n e := by
  unfold Dg
  refine Continuous.matrix_diagonal (continuous_pi fun i => ?_)
  unfold var' mean'
  refine Continuous.div_const ?_ _
  refine continuous_const.mul (continuous_finset_sum _ fun j _ => ?_)
  exact ((T_cont N j i).sub (continuous_const.mul
    (continuous_finset_sum _ fun j' _ => T_cont N j' i))).pow 2

lemma hfun_meas (i : Fin k) : Measurable fun e => hfun N n A c e i := by
  have hB : Continuous fun e => A + Dg N n e := continuous_const.add (Dg_cont N n)
  have heq : (fun e => hfun N n A c e i) = fun e =>
      ∑ j, c j * ((A + Dg N n e).det⁻¹ * (A + Dg N n e).adjugate j i) := by
    funext e
    simp [hfun, vecMul, dotProduct, Matrix.inv_def, Ring.inverse_eq_inv']
  rw [heq]
  refine Finset.measurable_sum _ fun j _ => ?_
  refine measurable_const.mul ?_
  exact (hB.matrix_det.measurable.inv).mul (hB.matrix_adjugate.matrix_elem j i).measurable

lemma hfun_bound (hA : A.PosDef) (hn : ∀ i, 1 ≤ n i) :
    ∃ C : ℝ, ∀ e i, |hfun N n A c e i| ≤ C := by
  obtain ⟨C, hC⟩ := bound_vecMul_inv A hA c
  refine ⟨C, fun e i => hC _ ?_ i⟩
  unfold Dg
  refine Matrix.PosSemidef.diagonal fun i => ?_
  exact div_nonneg (var'_nonneg _ (hn i)) (Nat.cast_nonneg _)

end Fns

end SKUnbiasedAux

open StochKriging.Unbiased SKUnbiasedAux Matrix

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {d k : ℕ} (x : Fin k → EuclideanSpace ℝ (Fin d)) (hx : Function.Injective x)
    (n : Fin k → ℕ) (hn : ∀ i, 2 ≤ n i) (β₀ : ℝ) (V : EuclideanSpace ℝ (Fin d) → ℝ≥0)
    (hV : ∀ i, 0 < V (x i)) (M : EuclideanSpace ℝ (Fin d) → Ω → ℝ)
    (ε : ℕ → EuclideanSpace ℝ (Fin d) → Ω → ℝ) (hA : Assumption1 P M ε V x)
    (x₀ : EuclideanSpace ℝ (Fin d)) :
    Integrable (fun ω => predictorHat P β₀ M ε x n x₀ ω - (β₀ + M x₀ ω)) P ∧
      ∫ ω, (predictorHat P β₀ M ε x n x₀ ω - (β₀ + M x₀ ω)) ∂P = 0 := by
  set N : ℕ := ∑ i, n i with hN
  have hnN : ∀ i, n i ≤ N := fun i =>
    Finset.single_le_sum (f := n) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  have hn0 : ∀ i, n i ≠ 0 := fun i => by have := hn i; omega
  set A := SigmaM P M x with hAdef
  set c := SigmaM0 P M x x₀ with hcdef
  have hApd : A.PosDef := hA.posDef k x hx
  let F : Ω → (Fin k × Fin N → ℝ) := fun ω p => ε p.2 (x p.1) ω
  have hTF : ∀ ω i j, j < n i → T N (F ω) j i = ε j (x i) ω := by
    intro ω i j hj
    have : j < N := lt_of_lt_of_le hj (hnN i)
    simp [T, this, F]
  -- pointwise identity
  have hS2 : ∀ ω, SigmaEpsHat β₀ M ε x n ω = Dg N n (F ω) := by
    intro ω
    unfold SigmaEpsHat Dg
    congr 1; funext i
    congr 1
    show var' (fun j => β₀ + M (x i) ω + ε j (x i) ω) (n i) = _
    rw [var'_shift _ (fun j => ε j (x i) ω) (hn0 i)]
    exact var'_congr fun j hj => (hTF ω i j hj).symm
  have hYb : ∀ ω, (Ybar β₀ M ε x n ω - fun _ => β₀) = fun i => M (x i) ω + Lfun N n (F ω) i := by
    intro ω; funext i
    show mean' (fun j => β₀ + M (x i) ω + ε j (x i) ω) (n i) - β₀ = _
    rw [mean'_shift _ (fun j => ε j (x i) ω) (hn0 i)]
    unfold Lfun
    rw [mean'_congr fun j hj => (hTF ω i j hj).symm]
    ring
  have hpt : ∀ ω, predictorHat P β₀ M ε x n x₀ ω - (β₀ + M x₀ ω) =
      ∑ i, hfun N n A c (F ω) i * M (x i) ω + ∑ i, hfun N n A c (F ω) i * Lfun N n (F ω) i
        - M x₀ ω := by
    intro ω
    unfold predictorHat
    rw [hS2, hYb, dotProduct_mulVec]
    simp only [dotProduct, ← Finset.sum_add_distrib, mul_add]
    simp only [hfun, hAdef, hcdef]
    ring
  -- measurability / integrability
  have hεm : ∀ i j, AEMeasurable (ε j (x i)) P := fun i j => (hA.noise_law i j).aemeasurable
  have hεint : ∀ i j, Integrable (ε j (x i)) P := fun i j =>
    (hA.noise_law i j).hasGaussianLaw.integrable
  have hMint : ∀ y, Integrable (M y) P := fun y => (hA.gaussian.hasGaussianLaw_eval y).integrable
  have hF : AEMeasurable F P := aemeasurable_pi_lambda _ fun p => hεm p.1 p.2
  obtain ⟨C, hC⟩ := hfun_bound N n A c hApd (fun i => by have := hn i; omega)
  have hwm : ∀ i, AEStronglyMeasurable (fun ω => hfun N n A c (F ω) i) P := fun i =>
    ((hfun_meas N n A c i).comp_aemeasurable hF).aestronglyMeasurable
  have hwb : ∀ i, ∀ᵐ ω ∂P, ‖hfun N n A c (F ω) i‖ ≤ C := fun i =>
    Filter.Eventually.of_forall fun ω => by simpa [Real.norm_eq_abs] using hC (F ω) i
  have hLeq : ∀ i ω, Lfun N n (F ω) i = (1 / (n i : ℝ)) * ∑ j ∈ Finset.range (n i), ε j (x i) ω :=
    fun i ω => by
      unfold Lfun mean'
      congr 1
      exact Finset.sum_congr rfl fun j hj => hTF ω i j (Finset.mem_range.1 hj)
  have hLint : ∀ i, Integrable (fun ω => Lfun N n (F ω) i) P := fun i => by
    simp_rw [hLeq i]
    exact (integrable_finsetSum _ fun j _ => hεint i j).const_mul _
  have hI1 : ∀ i, Integrable (fun ω => hfun N n A c (F ω) i * M (x i) ω) P := fun i =>
    (hMint (x i)).bdd_mul (hwm i) (hwb i)
  have hI2 : ∀ i, Integrable (fun ω => hfun N n A c (F ω) i * Lfun N n (F ω) i) P := fun i =>
    (hLint i).bdd_mul (hwm i) (hwb i)
  have hint : Integrable (fun ω => predictorHat P β₀ M ε x n x₀ ω - (β₀ + M x₀ ω)) P := by
    simp_rw [hpt]
    exact ((integrable_finsetSum _ fun i _ => hI1 i).add
      (integrable_finsetSum _ fun i _ => hI2 i)).sub (hMint x₀)
  refine ⟨hint, ?_⟩
  -- independence of noise and field
  have hJ1 : ∀ i, ∫ ω, hfun N n A c (F ω) i * M (x i) ω ∂P = 0 := by
    intro i
    have hφ : Measurable fun q : (Fin k × ℕ → ℝ) =>
        hfun N n A c (fun p : Fin k × Fin N => q (p.1, (p.2 : ℕ))) i :=
      (hfun_meas N n A c i).comp (measurable_pi_lambda _ fun p => measurable_pi_apply _)
    have hψ : Measurable fun f : (EuclideanSpace ℝ (Fin d) → ℝ) => f (x i) :=
      measurable_pi_apply _
    have hind : IndepFun (fun ω => hfun N n A c (F ω) i) (M (x i)) P :=
      hA.noise_indep_field.comp hφ hψ
    rw [hind.integral_fun_mul_eq_mul_integral (hwm i) (hMint (x i)).aestronglyMeasurable,
      hA.mean_zero, mul_zero]
  -- symmetry of the noise law
  have hJ2 : ∀ i, ∫ ω, hfun N n A c (F ω) i * Lfun N n (F ω) i ∂P = 0 := by
    intro i
    have hind : iIndepFun (fun (p : Fin k × Fin N) => ε p.2 (x p.1)) P :=
      hA.noise_indep.precomp (g := fun p : Fin k × Fin N => (p.1, (p.2 : ℕ)))
        (fun p q h => by
          simp only [Prod.mk.injEq] at h
          exact Prod.ext h.1 (Fin.ext h.2))
    have hind' : iIndepFun (fun (p : Fin k × Fin N) => fun ω => -ε p.2 (x p.1) ω) P :=
      hind.comp (fun _ => fun t : ℝ => -t) (fun _ => measurable_neg)
    have hneg : ∀ v : ℝ≥0, HasLaw (fun t : ℝ => -t) (gaussianReal 0 v) (gaussianReal 0 v) :=
      fun v => ⟨by fun_prop, by rw [gaussianReal_map_neg, neg_zero]⟩
    have hlaw1 := hind.hasLaw_pi (fun (p : Fin k × Fin N) => hA.noise_law p.1 p.2)
    have hlaw2 := hind'.hasLaw_pi (fun (p : Fin k × Fin N) => (hneg _).comp (hA.noise_law p.1 p.2))
    have hmap : P.map F = P.map (fun ω p => -F ω p) := by
      rw [hlaw1.map_eq]; exact hlaw2.map_eq.symm
    set G : (Fin k × Fin N → ℝ) → ℝ := fun e => hfun N n A c e i * Lfun N n e i with hG
    have hGm : Measurable G := (hfun_meas N n A c i).mul (Lfun_cont N n i).measurable
    have hGodd : ∀ e, G (fun p => -e p) = -G e := fun e => by
      simp only [hG, hfun_neg, Lfun_neg]; ring
    have hF' : AEMeasurable (fun ω p => -F ω p) P := by
      exact aemeasurable_pi_lambda _ fun p => (hεm p.1 p.2).neg
    have e1 : ∫ ω, G (F ω) ∂P = ∫ e, G e ∂(P.map F) :=
      (integral_map hF hGm.aestronglyMeasurable).symm
    have e2 : ∫ ω, G (fun p => -F ω p) ∂P = ∫ e, G e ∂(P.map (fun ω p => -F ω p)) :=
      (integral_map hF' hGm.aestronglyMeasurable).symm
    have e3 : ∫ ω, G (fun p => -F ω p) ∂P = -∫ ω, G (F ω) ∂P := by
      simp_rw [hGodd]; exact integral_neg _
    have : ∫ ω, G (F ω) ∂P = 0 := by
      have e4 : ∫ ω, G (F ω) ∂P = ∫ ω, G (fun p => -F ω p) ∂P := by rw [e1, hmap, ← e2]
      linarith
    exact this
  have hA1 : Integrable (fun ω => ∑ i, hfun N n A c (F ω) i * M (x i) ω) P :=
    integrable_finsetSum _ fun i _ => hI1 i
  have hA2 : Integrable (fun ω => ∑ i, hfun N n A c (F ω) i * Lfun N n (F ω) i) P :=
    integrable_finsetSum _ fun i _ => hI2 i
  have hA12 : Integrable (fun ω => ∑ i, hfun N n A c (F ω) i * M (x i) ω +
      ∑ i, hfun N n A c (F ω) i * Lfun N n (F ω) i) P := hA1.add hA2
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_sub hA12 (hMint x₀),
    integral_add hA1 hA2, integral_finsetSum _ fun i _ => hI1 i,
    integral_finsetSum _ fun i _ => hI2 i]
  simp [hJ1, hJ2, hA.mean_zero]
