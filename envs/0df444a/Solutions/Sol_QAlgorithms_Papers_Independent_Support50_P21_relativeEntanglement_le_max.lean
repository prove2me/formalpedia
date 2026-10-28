-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P21.relativeEntanglement_le_max
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T07:24:17.621496+00:00
-- url     : https://prove2.me/submissions/af60cd71-d803-48ae-b06b-64abe26b9d6a

import Mathlib
import Definitions.Def_QAlgorithms_Defs_BipartiteSeparability
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P21
import Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P21_relativeEntropy_sandwich
import Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P23_signed_entropy_properties

section X5mod_L13_Cpt
open Matrix Set
open scoped ComplexOrder Kronecker

namespace X5L13

lemma oct : OrderClosedTopology ℂ := Complex.orderClosedTopology

/-- the set of density matrices -/
def Dens (K : Type) [Fintype K] : Set (Matrix K K ℂ) := {A | QAlgorithms.IsDensityMatrix A}

variable {K : Type} [Fintype K] [DecidableEq K]

lemma dens_closed : IsClosed (Dens K) := by
  haveI := oct
  have e : Dens K = {A : Matrix K K ℂ | Aᴴ = A} ∩ (⋂ x : K → ℂ, {A | 0 ≤ star x ⬝ᵥ (A *ᵥ x)}) ∩
      {A | A.trace = 1} := by
    ext A
    simp only [Dens, QAlgorithms.IsDensityMatrix, Matrix.posSemidef_iff_dotProduct_mulVec, mem_inter_iff,
      mem_setOf_eq, mem_iInter]
    rfl
  rw [e]
  refine ((isClosed_eq continuous_id.matrix_conjTranspose continuous_id).inter
    (isClosed_iInter fun x => isClosed_le continuous_const ?_)).inter
    (isClosed_eq continuous_id.matrix_trace continuous_const)
  exact continuous_const.dotProduct (continuous_id.matrix_mulVec continuous_const)

lemma entry_le {A : Matrix K K ℂ} (hA : QAlgorithms.IsDensityMatrix A) (i j : K) : ‖A i j‖ ≤ 1 := by
  have hH := hA.1.1
  set U := hH.eigenvectorUnitary
  have hs := hH.spectral_theorem
  have hU : ∀ a b, ‖(U : Matrix K K ℂ) a b‖ ≤ 1 := fun a b => entry_norm_bound_of_unitary U.2 a b
  have e : A i j = ∑ k, (U : Matrix K K ℂ) i k * (hH.eigenvalues k : ℂ) *
      star ((U : Matrix K K ℂ) j k) := by
    conv_lhs => rw [hs]
    rw [Unitary.conjStarAlgAut_apply]
    simp [Matrix.mul_apply, Matrix.diagonal, Matrix.star_apply, Finset.sum_ite_eq', mul_assoc]
    simp only [U, Matrix.IsHermitian.eigenvectorUnitary_apply]
  have htr : ∑ k, hH.eigenvalues k = 1 := by
    have := hH.trace_eq_sum_eigenvalues
    rw [hA.2] at this
    have h2 := congrArg Complex.re this
    simp at h2; linarith
  rw [e]
  calc ‖∑ k, (U : Matrix K K ℂ) i k * (hH.eigenvalues k : ℂ) * star ((U : Matrix K K ℂ) j k)‖
      ≤ ∑ k, ‖(U : Matrix K K ℂ) i k * (hH.eigenvalues k : ℂ) * star ((U : Matrix K K ℂ) j k)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ k, hH.eigenvalues k := by
        refine Finset.sum_le_sum fun k _ => ?_
        rw [norm_mul, norm_mul, norm_star, Complex.norm_real, Real.norm_of_nonneg (hA.1.eigenvalues_nonneg k)]
        have h1 := hU i k; have h2 := hU j k
        have h3 := hA.1.eigenvalues_nonneg k
        calc ‖(U : Matrix K K ℂ) i k‖ * hH.eigenvalues k * ‖(U : Matrix K K ℂ) j k‖
            ≤ 1 * hH.eigenvalues k * 1 := by gcongr
          _ = _ := by ring
    _ = 1 := htr

lemma dens_compact : IsCompact (Dens K) := by
  have hc : IsCompact (Set.pi univ fun _ : K => Set.pi univ fun _ : K => Metric.closedBall (0 : ℂ) 1) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
  refine hc.of_isClosed_subset dens_closed fun A hA => ?_
  simp only [Set.mem_pi, mem_univ, forall_true_left, Metric.mem_closedBall, dist_zero_right]
  exact fun i j => entry_le hA i j

end X5L13
end X5mod_L13_Cpt

section X5mod_L13_Sep
open Matrix Set
open scoped ComplexOrder Kronecker

namespace X5L13
open QAlgorithms.Entanglement (IsSeparableDensity)

variable {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Nonempty I] [Nonempty J]

/-- the separable mixture map with `q` terms -/
def F (q : ℕ) (p : (Fin q → ℝ) × (Fin q → Matrix I I ℂ) × (Fin q → Matrix J J ℂ)) :
    Matrix (I × J) (I × J) ℂ :=
  ∑ j, ((p.1 j : ℝ) : ℂ) • kronecker (p.2.1 j) (p.2.2 j)

def Kq (I J : Type) [Fintype I] [Fintype J] (q : ℕ) :
    Set ((Fin q → ℝ) × (Fin q → Matrix I I ℂ) × (Fin q → Matrix J J ℂ)) :=
  stdSimplex ℝ (Fin q) ×ˢ (Set.pi univ (fun _ => Dens I) ×ˢ Set.pi univ (fun _ => Dens J))

lemma F_cont (q : ℕ) : Continuous (F (I := I) (J := J) q) := by
  unfold F
  refine continuous_finset_sum _ fun j _ => ?_
  refine (Complex.continuous_ofReal.comp ((continuous_apply j).comp continuous_fst)).smul ?_
  have hA : Continuous fun p : (Fin q → ℝ) × (Fin q → Matrix I I ℂ) × (Fin q → Matrix J J ℂ) =>
      p.2.1 j := (continuous_apply j).comp (continuous_fst.comp continuous_snd)
  have hB : Continuous fun p : (Fin q → ℝ) × (Fin q → Matrix I I ℂ) × (Fin q → Matrix J J ℂ) =>
      p.2.2 j := (continuous_apply j).comp (continuous_snd.comp continuous_snd)
  refine continuous_matrix fun a b => ?_
  simp only [kronecker, kroneckerMap_apply]
  exact (hA.matrix_elem a.1 b.1).mul (hB.matrix_elem a.2 b.2)

lemma Kq_compact (q : ℕ) : IsCompact (Kq I J q) :=
  (isCompact_stdSimplex _ _).prod
    ((isCompact_univ_pi fun _ => dens_compact).prod (isCompact_univ_pi fun _ => dens_compact))

def Pset (I J : Type) [Fintype I] [Fintype J] : Set (Matrix (I × J) (I × J) ℂ) :=
  {X | ∃ A B, QAlgorithms.IsDensityMatrix A ∧ QAlgorithms.IsDensityMatrix B ∧ X = kronecker A B}

lemma csmul (r : ℝ) (X : Matrix (I × J) (I × J) ℂ) : ((r : ℂ) • X) = r • X := by
  ext a b; simp

lemma sep_eq : {X : Matrix (I × J) (I × J) ℂ | IsSeparableDensity X} =
    ⋃ q ∈ Finset.range (Module.finrank ℝ (Matrix (I × J) (I × J) ℂ) + 2), F q '' Kq I J q := by
  ext X
  simp only [mem_setOf_eq, mem_iUnion, Finset.mem_range, mem_image]
  constructor
  · rintro ⟨q, w, A, B, hw, hs, hd, rfl⟩
    have hmem : (∑ j, ((w j : ℝ) : ℂ) • kronecker (A j) (B j)) ∈ convexHull ℝ (Pset I J) := by
      simp only [csmul]
      exact (convex_convexHull ℝ _).sum_mem (fun j _ => hw j) hs
        (fun j _ => subset_convexHull ℝ _ ⟨A j, B j, (hd j).1, (hd j).2, rfl⟩)
    obtain ⟨ι, hι, z, v, hz, hai, hv, hvs, hx⟩ := eq_pos_convex_span_of_mem_convexHull hmem
    have hcard := hai.card_le_finrank_succ
    have hfr := Submodule.finrank_le (vectorSpan ℝ (range z))
    have hP : ∀ i, ∃ A B, QAlgorithms.IsDensityMatrix A ∧ QAlgorithms.IsDensityMatrix B ∧
        z i = kronecker A B := fun i => hz ⟨i, rfl⟩
    choose A' B' hA' hB' hzAB using hP
    set e := Fintype.equivFin ι
    refine ⟨Fintype.card ι, by omega, (v ∘ e.symm, A' ∘ e.symm, B' ∘ e.symm), ⟨?_, ?_⟩, ?_⟩
    · refine ⟨fun j => (hv _).le, ?_⟩
      simp only [Function.comp]
      rw [Equiv.sum_comp e.symm v]; exact hvs
    · simp only [Set.mem_pi, mem_univ, forall_true_left, Function.comp]
      exact ⟨fun j _ => hA' _, fun j _ => hB' _⟩
    · rw [← hx]
      unfold F
      simp only [Function.comp, csmul]
      rw [Equiv.sum_comp e.symm (fun i => v i • kronecker (A' i) (B' i))]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hzAB]
  · rintro ⟨q, -, ⟨w, A, B⟩, ⟨⟨hw, hs⟩, hA, hB⟩, rfl⟩
    simp only [Set.mem_pi, mem_univ, forall_true_left] at hA hB
    exact ⟨q, w, A, B, hw, hs, fun j => ⟨hA j, hB j⟩, rfl⟩

lemma sep_compact : IsCompact {X : Matrix (I × J) (I × J) ℂ | IsSeparableDensity X} := by
  rw [sep_eq]
  exact Finset.isCompact_biUnion _ fun q _ => (Kq_compact q).image (F_cont q)

lemma sep_dens {X : Matrix (I × J) (I × J) ℂ} (h : IsSeparableDensity X) :
    QAlgorithms.IsDensityMatrix X := by
  obtain ⟨q, w, A, B, hw, hs, hd, rfl⟩ := h
  refine ⟨?_, ?_⟩
  · refine Matrix.posSemidef_sum _ fun j _ => ?_
    rw [csmul]
    exact ((hd j).1.1.kronecker (hd j).2.1).smul (hw j)
  · rw [Matrix.trace_sum]
    have ht : ∀ j, ((A j).kronecker (B j)).trace = 1 := fun j => by
      rw [show (A j).kronecker (B j) = A j ⊗ₖ B j from rfl, Matrix.trace_kronecker, (hd j).1.2,
        (hd j).2.2, mul_one]
    simp only [Matrix.trace_smul, ht, smul_eq_mul, mul_one]
    exact_mod_cast hs

lemma dens_ex (K : Type) [Fintype K] [DecidableEq K] [Nonempty K] :
    ∃ A : Matrix K K ℂ, QAlgorithms.IsDensityMatrix A := by
  obtain ⟨k0⟩ := ‹Nonempty K›
  refine ⟨Matrix.diagonal (Pi.single k0 1), PosSemidef.diagonal ?_, ?_⟩
  · intro k; by_cases h : k = k0
    · subst h; simp
    · simp [Pi.single_apply, h]
  · rw [Matrix.trace_diagonal]; simp

lemma sep_nonempty : {X : Matrix (I × J) (I × J) ℂ | IsSeparableDensity X}.Nonempty := by
  obtain ⟨A, hA⟩ := dens_ex I
  obtain ⟨B, hB⟩ := dens_ex J
  refine ⟨kronecker A B, 1, fun _ => 1, fun _ => A, fun _ => B, fun _ => zero_le_one, by simp,
    fun _ => ⟨hA, hB⟩, by simp⟩

end X5L13
end X5mod_L13_Sep

section X5mod_L13_Thm
open Matrix Set Filter Topology
open scoped ComplexOrder

namespace X5L13
open QAlgorithms.Entanglement (IsSeparableDensity)
open QAlgorithms.Papers.Independent.Information100.P71 (SupportIncluded)
open QAlgorithms.Papers.Independent.Dependency50.P35 (tr)
open QAlgorithms.Papers.Independent.Support50.P21 (unnormalizedRelativeBits eRelative eMax)

lemma fin' {K : Type} [Fintype K] [DecidableEq K] (X : Matrix K K ℂ) (f : ℝ → ℝ) :
    ContinuousOn f (spectrum ℝ X) :=
  (Matrix.finite_real_spectrum (A := X)).continuousOn f

lemma bits_eq {K : Type} [Fintype K] [DecidableEq K] (R S : Matrix K K ℂ) (hR : R.IsHermitian) :
    unnormalizedRelativeBits R S = (((Real.log 2)⁻¹ : ℝ) : EReal) *
      QAlgorithms.Papers.Independent.Dependency50.P21.relativeEntropy R S := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold unnormalizedRelativeBits QAlgorithms.Papers.Independent.Dependency50.P21.relativeEntropy
  by_cases h : SupportIncluded R S
  · have h' : QAlgorithms.Papers.Independent.Dependency50.P21.IsSupported R S := h
    rw [if_pos h, if_pos h', ← EReal.coe_mul]
    congr 1
    have e : ∀ X : Matrix K K ℂ, cfc (fun x : ℝ => Real.logb 2 x) X = (Real.log 2)⁻¹ • cfc Real.log X := by
      intro X
      rw [show (fun x : ℝ => Real.logb 2 x) = fun x => (Real.log 2)⁻¹ * Real.log x by
        funext x; rw [Real.logb]; ring]
      exact cfc_const_mul _ _ X (fin' _ _)
    have hx : R * cfc Real.log R = cfc (fun x : ℝ => x * Real.log x) R := by
      have : R * cfc Real.log R = cfc (fun x : ℝ => x) R * cfc Real.log R := by
        rw [cfc_id' ℝ R hR.isSelfAdjoint]
      rw [this, ← cfc_mul _ _ R (fin' _ _) (fin' _ _)]
    unfold tr
    rw [e, e, ← smul_sub, Matrix.mul_smul, Matrix.trace_smul, Matrix.mul_sub, hx]
    simp only [Complex.smul_re, smul_eq_mul, Matrix.trace_sub, Complex.sub_re]
  · have h' : ¬ QAlgorithms.Papers.Independent.Dependency50.P21.IsSupported R S := h
    rw [if_neg h, if_neg h']
    exact (EReal.coe_mul_top_of_pos (inv_pos.mpr hl2)).symm

variable {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Nonempty I] [Nonempty J]

lemma bits_lsc (rho : Matrix (I × J) (I × J) ℂ) (hrho : QAlgorithms.IsDensityMatrix rho) :
    LowerSemicontinuousOn (fun s => unnormalizedRelativeBits rho s)
      {X : Matrix (I × J) (I × J) ℂ | IsSeparableDensity X} := by
  have hU := (QAlgorithms.Papers.Independent.Next46.P23.signed_entropy_properties
    (I := I × J)).2.2.2.2.2.2.1.2
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set c : ℝ := (Real.log 2)⁻¹ with hc
  have hc0 : 0 < c := inv_pos.mpr hl2
  have hcc : ∀ z : EReal, (c : EReal) * (((c⁻¹ : ℝ) : EReal) * z) = z := by
    intro z
    rw [← mul_assoc, ← EReal.coe_mul, mul_inv_cancel₀ hc0.ne', EReal.coe_one, one_mul]
  intro s0 hs0 y hy
  simp only [bits_eq rho _ hrho.1.1] at hy ⊢
  obtain ⟨y2, hy1, hy2⟩ := exists_between hy
  have key : ((c⁻¹ : ℝ) : EReal) * y2 <
      QAlgorithms.Papers.Independent.Dependency50.P21.relativeEntropy rho s0 := by
    rw [← hcc y2] at hy2
    exact lt_of_mul_lt_mul_left hy2 (by exact_mod_cast hc0.le)
  have hp0 : (rho, s0) ∈ {p : Matrix (I × J) (I × J) ℂ × Matrix (I × J) (I × J) ℂ |
      QAlgorithms.IsDensityMatrix p.1 ∧ QAlgorithms.IsDensityMatrix p.2} := ⟨hrho, sep_dens hs0⟩
  have hev := hU (rho, s0) hp0 (-(((c⁻¹ : ℝ) : EReal) * y2)) (by
    show -(QAlgorithms.Papers.Independent.Dependency50.P21.relativeEntropy rho s0) < _
    exact EReal.neg_lt_neg_iff.mpr key)
  have ht : Tendsto (fun s : Matrix (I × J) (I × J) ℂ => (rho, s))
      (𝓝[{X : Matrix (I × J) (I × J) ℂ | IsSeparableDensity X}] s0)
      (𝓝[{p : Matrix (I × J) (I × J) ℂ × Matrix (I × J) (I × J) ℂ |
        QAlgorithms.IsDensityMatrix p.1 ∧ QAlgorithms.IsDensityMatrix p.2}] (rho, s0)) :=
    ((continuous_const.prodMk continuous_id).continuousWithinAt).tendsto_nhdsWithin
      fun s hs => ⟨hrho, sep_dens hs⟩
  filter_upwards [ht.eventually hev] with s hs
  have h1 : ((c⁻¹ : ℝ) : EReal) * y2 <
      QAlgorithms.Papers.Independent.Dependency50.P21.relativeEntropy rho s := by
    have : -(QAlgorithms.Papers.Independent.Dependency50.P21.relativeEntropy rho s) <
        -(((c⁻¹ : ℝ) : EReal) * y2) := hs
    exact EReal.neg_lt_neg_iff.mp this
  have h2 := mul_le_mul_of_nonneg_left h1.le (show (0 : EReal) ≤ (c : EReal) by exact_mod_cast hc0.le)
  rw [hcc] at h2
  exact lt_of_lt_of_le hy1 h2

theorem main (rho : Matrix (I × J) (I × J) ℂ) (hrho : QAlgorithms.IsDensityMatrix rho) :
    eRelative rho ≤ eMax rho ∧
    ∃ sigma : Matrix (I × J) (I × J) ℂ, IsSeparableDensity sigma ∧
      unnormalizedRelativeBits rho sigma = eRelative rho := by
  refine ⟨?_, ?_⟩
  · unfold eRelative eMax
    refine le_sInf ?_
    rintro _ ⟨σ, hσ, rfl⟩
    refine le_trans (sInf_le (show unnormalizedRelativeBits rho σ ∈ {v | ∃ sigma : Matrix (I × J) (I × J) ℂ,
      IsSeparableDensity sigma ∧ v = unnormalizedRelativeBits rho sigma} from ⟨σ, hσ, rfl⟩)) ?_
    exact (QAlgorithms.Papers.Independent.Support50.P21.relativeEntropy_sandwich rho σ hrho (sep_dens hσ)).2
  · obtain ⟨a, ha, hmin⟩ := (bits_lsc rho hrho).exists_isMinOn sep_nonempty sep_compact
    unfold eRelative
    refine ⟨a, ha, le_antisymm ?_ (sInf_le ⟨a, ha, rfl⟩)⟩
    refine le_sInf ?_
    rintro _ ⟨σ, hσ, rfl⟩
    exact hmin hσ

end X5L13
end X5mod_L13_Thm

noncomputable section

open QAlgorithms QAlgorithms.Entanglement Filter

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Support50.P21
open QAlgorithms.Papers.Independent.Information100.P63 (Mat)
open QAlgorithms.Papers.Independent.Dependency50.P35 (tr elog maxRelative)

section Statements

variable {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

variable [Nonempty I] [Nonempty J]

theorem solution (rho : Mat (I × J)) (hrho : IsDensityMatrix rho) :
    eRelative rho ≤ eMax rho ∧
    ∃ sigma : Mat (I × J), IsSeparableDensity sigma ∧ unnormalizedRelativeBits rho sigma = eRelative rho :=
  X5L13.main rho hrho

end Statements

end
