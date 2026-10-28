-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P21.maxRelative_entanglement_monotone
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T07:49:27.508121+00:00
-- url     : https://prove2.me/submissions/2043ec7b-7fa5-4724-b509-2b477572eb40

import Mathlib
import Definitions.Def_QAlgorithms_Defs_BipartiteSeparability
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P21

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

section X5mod_G_Base
open Matrix Set Filter Topology
open scoped ComplexOrder Kronecker

namespace X5G
open QAlgorithms.Entanglement (IsSeparableDensity)
open QAlgorithms.Papers.Independent.Dependency50.P35 (tr maxRelative)
open QAlgorithms.Papers.Independent.Support50.P21 (eMax)
open X5L13

section General
variable {K : Type} [Fintype K] [DecidableEq K]

lemma psd_re {X : Matrix K K ℂ} (h : X.PosSemidef) : 0 ≤ X.trace.re :=
  (Complex.nonneg_iff.mp h.trace_nonneg).1

lemma psd_closed : IsClosed {A : Matrix K K ℂ | A.PosSemidef} := by
  haveI := oct
  have e : {A : Matrix K K ℂ | A.PosSemidef} = {A : Matrix K K ℂ | Aᴴ = A} ∩
      (⋂ x : K → ℂ, {A | 0 ≤ star x ⬝ᵥ (A *ᵥ x)}) := by
    ext A
    simp only [Matrix.posSemidef_iff_dotProduct_mulVec, mem_inter_iff, mem_setOf_eq, mem_iInter]
    rfl
  rw [e]
  refine (isClosed_eq continuous_id.matrix_conjTranspose continuous_id).inter
    (isClosed_iInter fun x => isClosed_le continuous_const ?_)
  exact continuous_const.dotProduct (continuous_id.matrix_mulVec continuous_const)

/-- feasibility of the exponent `l` in the max-relative entropy -/
def Feas (rho sigma : Matrix K K ℂ) (l : ℝ) : Prop :=
  ((((2 : ℝ) ^ l : ℝ) : ℂ) • sigma - rho).PosSemidef

lemma feas_mono {rho sigma : Matrix K K ℂ} (hσ : sigma.PosSemidef) {l l' : ℝ} (h : l ≤ l')
    (hf : Feas rho sigma l) : Feas rho sigma l' := by
  unfold Feas at *
  have e : (((2 : ℝ) ^ l' : ℝ) : ℂ) • sigma - rho = ((((2 : ℝ) ^ l' - (2 : ℝ) ^ l : ℝ) : ℂ) • sigma) +
      ((((2 : ℝ) ^ l : ℝ) : ℂ) • sigma - rho) := by
    simp only [Complex.ofReal_sub, sub_smul]; abel
  rw [e]
  refine Matrix.PosSemidef.add (hσ.smul ?_) hf
  have : (2 : ℝ) ^ l ≤ (2 : ℝ) ^ l' := Real.rpow_le_rpow_of_exponent_le (by norm_num) h
  exact_mod_cast (sub_nonneg.mpr this)

lemma maxRel_le {rho sigma : Matrix K K ℂ} {l : ℝ} (hf : Feas rho sigma l) :
    maxRelative rho sigma ≤ l := sInf_le ⟨l, rfl, hf⟩

lemma feas_of_lt {rho sigma : Matrix K K ℂ} (hσ : sigma.PosSemidef) {l : ℝ}
    (h : maxRelative rho sigma < l) : Feas rho sigma l := by
  unfold maxRelative at h
  obtain ⟨w, ⟨l', rfl, hl⟩, hw⟩ := sInf_lt_iff.mp h
  exact feas_mono hσ (EReal.coe_lt_coe_iff.mp hw).le hl

lemma feas_lim {rho sigma : Matrix K K ℂ} {l : ℝ}
    (h : ∀ k : ℕ, Feas rho sigma (l + 1 / ((k : ℝ) + 1))) : Feas rho sigma l := by
  have ht : Tendsto (fun k : ℕ => l + 1 / ((k : ℝ) + 1)) atTop (𝓝 l) := by
    have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_add l
    simpa using this
  have ht2 : Tendsto (fun k : ℕ => (((2 : ℝ) ^ (l + 1 / ((k : ℝ) + 1)) : ℝ) : ℂ) • sigma - rho) atTop
      (𝓝 ((((2 : ℝ) ^ l : ℝ) : ℂ) • sigma - rho)) := by
    have hc : Continuous fun x : ℝ => (((2 : ℝ) ^ x : ℝ) : ℂ) • sigma - rho :=
      ((Complex.continuous_ofReal.comp (Real.continuous_const_rpow (by norm_num : (2 : ℝ) ≠ 0))).smul
        continuous_const).sub continuous_const
    exact (hc.tendsto l).comp ht
  exact psd_closed.mem_of_tendsto ht2 (Eventually.of_forall h)

lemma feas_of_le {rho sigma : Matrix K K ℂ} (hσ : sigma.PosSemidef) {l : ℝ}
    (h : maxRelative rho sigma ≤ l) : Feas rho sigma l := by
  refine feas_lim fun k => feas_of_lt hσ (lt_of_le_of_lt h ?_)
  have : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
  exact_mod_cast (by linarith : l < l + 1 / ((k : ℝ) + 1))

lemma feas_nonneg {rho sigma : Matrix K K ℂ} (hρ : QAlgorithms.IsDensityMatrix rho)
    (hσ : QAlgorithms.IsDensityMatrix sigma) {l : ℝ} (hf : Feas rho sigma l) : 0 ≤ l := by
  have h := psd_re hf
  rw [Matrix.trace_sub, Matrix.trace_smul, hσ.2, hρ.2] at h
  simp at h
  by_contra hl; push_neg at hl
  have : (2 : ℝ) ^ l < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) hl
  linarith

lemma maxRel_nonneg {rho sigma : Matrix K K ℂ} (hρ : QAlgorithms.IsDensityMatrix rho)
    (hσ : QAlgorithms.IsDensityMatrix sigma) : 0 ≤ maxRelative rho sigma := by
  refine le_sInf ?_
  rintro _ ⟨l, rfl, hf⟩
  exact_mod_cast feas_nonneg hρ hσ hf

lemma one_sub_psd {rho : Matrix K K ℂ} (hρ : QAlgorithms.IsDensityMatrix rho) :
    (1 - rho).PosSemidef := by
  have hH := hρ.1.1
  have hs := hH.spectral_theorem
  set U := hH.eigenvectorUnitary
  have hle : ∀ k, hH.eigenvalues k ≤ 1 := by
    intro k
    have htr : ∑ k, hH.eigenvalues k = 1 := by
      have := hH.trace_eq_sum_eigenvalues
      rw [hρ.2] at this
      have h2 := congrArg Complex.re this
      simp at h2; linarith
    rw [← htr]
    exact Finset.single_le_sum (fun i _ => hρ.1.eigenvalues_nonneg i) (Finset.mem_univ k)
  have hD : (Matrix.diagonal (fun k => ((1 - hH.eigenvalues k : ℝ) : ℂ))).PosSemidef := by
    refine PosSemidef.diagonal fun k => ?_
    have := sub_nonneg.mpr (hle k)
    show (0 : ℂ) ≤ _
    exact_mod_cast this
  have e : 1 - rho = (U : Matrix K K ℂ) * Matrix.diagonal (fun k => ((1 - hH.eigenvalues k : ℝ) : ℂ)) *
      (U : Matrix K K ℂ)ᴴ := by
    have hUU : (U : Matrix K K ℂ) * (U : Matrix K K ℂ)ᴴ = 1 := by
      have := U.2; rw [Matrix.mem_unitaryGroup_iff] at this; exact this
    conv_lhs => rw [hs, Unitary.conjStarAlgAut_apply]
    rw [show Matrix.diagonal (fun k => ((1 - hH.eigenvalues k : ℝ) : ℂ)) =
      1 - Matrix.diagonal (RCLike.ofReal ∘ hH.eigenvalues) by
        ext a b; by_cases h : a = b
        · subst h; simp
        · simp [Matrix.diagonal, Matrix.one_apply, h]]
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hUU]
    rfl
  rw [e]; exact hD.mul_mul_conjTranspose_same _

end General

section Bip
variable {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Nonempty I] [Nonempty J]

lemma emax_le {rho sigma : Matrix (I × J) (I × J) ℂ} (h : IsSeparableDensity sigma) :
    eMax rho ≤ maxRelative rho sigma := sInf_le ⟨sigma, h, rfl⟩

lemma mm_dens (K : Type) [Fintype K] [DecidableEq K] [Nonempty K] :
    QAlgorithms.IsDensityMatrix (((Fintype.card K : ℂ)⁻¹) • (1 : Matrix K K ℂ)) := by
  have hc : (0 : ℝ) < Fintype.card K := by exact_mod_cast Fintype.card_pos
  refine ⟨?_, ?_⟩
  · have : ((Fintype.card K : ℂ)⁻¹) = (((Fintype.card K : ℝ)⁻¹ : ℝ) : ℂ) := by push_cast; rfl
    rw [this]
    exact PosSemidef.one.smul (by exact_mod_cast (inv_pos.mpr hc).le)
  · rw [Matrix.trace_smul, Matrix.trace_one]
    have : (Fintype.card K : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
    simp [this]

lemma emax_fin {rho : Matrix (I × J) (I × J) ℂ} (hρ : QAlgorithms.IsDensityMatrix rho) :
    eMax rho ≤ ((Real.logb 2 (Fintype.card I * Fintype.card J) : ℝ) : EReal) := by
  set σ0 := kronecker (((Fintype.card I : ℂ)⁻¹) • (1 : Matrix I I ℂ))
    (((Fintype.card J : ℂ)⁻¹) • (1 : Matrix J J ℂ))
  have hsep : IsSeparableDensity σ0 :=
    ⟨1, fun _ => 1, fun _ => _, fun _ => _, fun _ => zero_le_one, by simp,
      fun _ => ⟨mm_dens I, mm_dens J⟩, by simp [σ0]⟩
  refine (emax_le hsep).trans (maxRel_le ?_)
  unfold Feas
  have hI : (0 : ℝ) < Fintype.card I := by exact_mod_cast Fintype.card_pos
  have hJ : (0 : ℝ) < Fintype.card J := by exact_mod_cast Fintype.card_pos
  have e : (((2 : ℝ) ^ Real.logb 2 (Fintype.card I * Fintype.card J) : ℝ) : ℂ) • σ0 = 1 := by
    rw [Real.rpow_logb (by norm_num) (by norm_num) (by positivity)]
    have hI' : (Fintype.card I : ℂ) ≠ 0 := by exact_mod_cast hI.ne'
    have hJ' : (Fintype.card J : ℂ) ≠ 0 := by exact_mod_cast hJ.ne'
    ext a b
    simp only [σ0, Matrix.smul_apply, Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.one_apply,
      smul_eq_mul]
    by_cases h1 : a.1 = b.1 <;> by_cases h2 : a.2 = b.2 <;>
      simp [h1, h2, Prod.ext_iff] <;> field_simp
  rw [e]; exact one_sub_psd hρ

/-- finiteness, nonnegativity and attainment of `eMax` -/
theorem attain {rho : Matrix (I × J) (I × J) ℂ} (hρ : QAlgorithms.IsDensityMatrix rho) :
    ∃ z : ℝ, 0 ≤ z ∧ eMax rho = (z : EReal) ∧
      ∃ sigma, IsSeparableDensity sigma ∧ Feas rho sigma z ∧ maxRelative rho sigma = eMax rho := by
  have h0 : 0 ≤ eMax rho := le_sInf (by
    rintro _ ⟨σ, hσ, rfl⟩; exact maxRel_nonneg hρ (sep_dens hσ))
  have hfin := emax_fin hρ
  have hne : eMax rho ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top _) hfin
  have hnb : eMax rho ≠ ⊥ := ne_bot_of_le_ne_bot (by simp) h0
  set z := (eMax rho).toReal
  have hz : eMax rho = (z : EReal) := (EReal.coe_toReal hne hnb).symm
  refine ⟨z, by exact_mod_cast hz ▸ h0, hz, ?_⟩
  set C : ℕ → Set (Matrix (I × J) (I × J) ℂ) := fun k =>
    {σ | IsSeparableDensity σ} ∩ {σ | Feas rho σ (z + 1 / ((k : ℝ) + 1))}
  have hcl : ∀ k, IsClosed (C k) := by
    intro k
    refine sep_compact.isClosed.inter ?_
    have hc : Continuous fun σ : Matrix (I × J) (I × J) ℂ =>
        (((2 : ℝ) ^ (z + 1 / ((k : ℝ) + 1)) : ℝ) : ℂ) • σ - rho :=
      by fun_prop
    exact psd_closed.preimage hc
  have hne' : ∀ k, (C k).Nonempty := by
    intro k
    have hlt : eMax rho < ((z + 1 / ((k : ℝ) + 1) : ℝ) : EReal) := by
      rw [hz]; exact_mod_cast (by have : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
                                  linarith : z < z + 1 / ((k : ℝ) + 1))
    obtain ⟨_, ⟨σ, hσ, rfl⟩, hv⟩ := sInf_lt_iff.mp hlt
    exact ⟨σ, hσ, feas_of_lt (sep_dens hσ).1 hv⟩
  have hdec : ∀ k, C (k + 1) ⊆ C k := by
    rintro k σ ⟨hσ, hf⟩
    refine ⟨hσ, feas_mono (sep_dens hσ).1 ?_ hf⟩
    have : (1 : ℝ) / ((((k + 1 : ℕ) : ℝ)) + 1) ≤ 1 / ((k : ℝ) + 1) := by
      apply one_div_le_one_div_of_le (by positivity); push_cast; linarith
    linarith
  obtain ⟨σ, hσ⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed C hdec hne'
    (sep_compact.of_isClosed_subset (hcl 0) inter_subset_left) hcl
  simp only [mem_iInter] at hσ
  have hsep := (hσ 0).1
  have hF : Feas rho σ z := feas_lim fun k => (hσ k).2
  exact ⟨σ, hsep, hF, le_antisymm (hz ▸ maxRel_le hF) (emax_le hsep)⟩

end Bip
end X5G
end X5mod_G_Base

section X5mod_G_Simple
open Matrix Set Filter Topology
open scoped ComplexOrder Kronecker

namespace X5G
open QAlgorithms.Entanglement (IsSeparableDensity)
open QAlgorithms.Papers.Independent.Dependency50.P35 (tr maxRelative)
open QAlgorithms.Papers.Independent.Support50.P21 (eMax)
open X5L13

lemma kr_eq {m n : Type} (A : Matrix m m ℂ) (B : Matrix n n ℂ) : kronecker A B = A ⊗ₖ B := rfl

section General
variable {K : Type} [Fintype K] [DecidableEq K]

lemma unit_mul {W : Matrix K K ℂ} (hW : W ∈ unitaryGroup K ℂ) : Wᴴ * W = 1 :=
  (Matrix.mem_unitaryGroup_iff'.mp hW)

lemma mul_unit {W : Matrix K K ℂ} (hW : W ∈ unitaryGroup K ℂ) : W * Wᴴ = 1 :=
  (Matrix.mem_unitaryGroup_iff.mp hW)

lemma dens_conj {W : Matrix K K ℂ} (hW : W ∈ unitaryGroup K ℂ) {A : Matrix K K ℂ}
    (hA : QAlgorithms.IsDensityMatrix A) : QAlgorithms.IsDensityMatrix (W * A * Wᴴ) := by
  refine ⟨hA.1.mul_mul_conjTranspose_same W, ?_⟩
  rw [Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc, unit_mul hW, Matrix.mul_one, hA.2]

lemma feas_conj_iff {W : Matrix K K ℂ} (hW : W ∈ unitaryGroup K ℂ) (rho sigma : Matrix K K ℂ) (l : ℝ) :
    Feas (W * rho * Wᴴ) (W * sigma * Wᴴ) l ↔ Feas rho sigma l := by
  unfold Feas
  have e : (((2 : ℝ) ^ l : ℝ) : ℂ) • (W * sigma * Wᴴ) - W * rho * Wᴴ =
      W * ((((2 : ℝ) ^ l : ℝ) : ℂ) • sigma - rho) * Wᴴ := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul]
  rw [e]
  constructor
  · intro h
    have := h.mul_mul_conjTranspose_same Wᴴ
    rwa [conjTranspose_conjTranspose, ← Matrix.mul_assoc, ← Matrix.mul_assoc, unit_mul hW,
      Matrix.one_mul, Matrix.mul_assoc, unit_mul hW, Matrix.mul_one] at this
  · intro h; exact h.mul_mul_conjTranspose_same W

lemma maxRel_conj {W : Matrix K K ℂ} (hW : W ∈ unitaryGroup K ℂ) (rho sigma : Matrix K K ℂ) :
    maxRelative (W * rho * Wᴴ) (W * sigma * Wᴴ) = maxRelative rho sigma := by
  unfold maxRelative
  congr 1
  ext v
  simp only [mem_setOf_eq]
  exact exists_congr fun l => and_congr_right fun _ => feas_conj_iff hW rho sigma l

end General

section Bip
variable {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Nonempty I] [Nonempty J]

theorem zero_iff {rho : Matrix (I × J) (I × J) ℂ} (hρ : QAlgorithms.IsDensityMatrix rho) :
    eMax rho = 0 ↔ IsSeparableDensity rho := by
  constructor
  · intro h0
    obtain ⟨z, -, hz, σ, hσ, hF, -⟩ := attain hρ
    have hz0 : z = 0 := by rw [h0] at hz; exact_mod_cast hz.symm
    rw [hz0] at hF
    unfold Feas at hF
    simp only [Real.rpow_zero, Complex.ofReal_one, one_smul] at hF
    have htr : (σ - rho).trace = 0 := by rw [Matrix.trace_sub, (sep_dens hσ).2, hρ.2, sub_self]
    have := hF.trace_eq_zero_iff.mp htr
    rw [sub_eq_zero] at this
    rwa [← this]
  · intro h
    refine le_antisymm ((emax_le h).trans (maxRel_le (l := 0) ?_)) ?_
    · unfold Feas; simp only [Real.rpow_zero, Complex.ofReal_one, one_smul, sub_self]
      exact PosSemidef.zero
    · exact le_sInf (by rintro _ ⟨σ, hσ, rfl⟩; exact maxRel_nonneg hρ (sep_dens hσ))

lemma kron_unit {U : Matrix I I ℂ} {V : Matrix J J ℂ} (hU : U ∈ unitaryGroup I ℂ)
    (hV : V ∈ unitaryGroup J ℂ) : kronecker U V ∈ unitaryGroup (I × J) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, kr_eq, star_eq_conjTranspose, conjTranspose_kronecker,
    ← mul_kronecker_mul, mul_unit hU, mul_unit hV, one_kronecker_one]

lemma sep_conj {U : Matrix I I ℂ} {V : Matrix J J ℂ} (hU : U ∈ unitaryGroup I ℂ)
    (hV : V ∈ unitaryGroup J ℂ) {σ : Matrix (I × J) (I × J) ℂ} (h : IsSeparableDensity σ) :
    IsSeparableDensity (kronecker U V * σ * (kronecker U V)ᴴ) := by
  obtain ⟨q, w, A, B, hw, hs, hd, rfl⟩ := h
  refine ⟨q, w, fun j => U * A j * Uᴴ, fun j => V * B j * Vᴴ, hw, hs,
    fun j => ⟨dens_conj hU (hd j).1, dens_conj hV (hd j).2⟩, ?_⟩
  rw [Matrix.mul_sum, Matrix.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.mul_smul, Matrix.smul_mul, kr_eq, kr_eq, kr_eq, conjTranspose_kronecker,
    ← mul_kronecker_mul, ← mul_kronecker_mul]

theorem unitary_inv (rho : Matrix (I × J) (I × J) ℂ) (U : unitaryGroup I ℂ) (V : unitaryGroup J ℂ) :
    eMax (QAlgorithms.conjSuperop (kronecker (U : Matrix I I ℂ) (V : Matrix J J ℂ)) rho) = eMax rho := by
  unfold QAlgorithms.conjSuperop
  set W := kronecker (U : Matrix I I ℂ) (V : Matrix J J ℂ)
  have hW : W ∈ unitaryGroup (I × J) ℂ := kron_unit U.2 V.2
  have hU' : (U : Matrix I I ℂ)ᴴ ∈ unitaryGroup I ℂ := (star U).2
  have hV' : (V : Matrix J J ℂ)ᴴ ∈ unitaryGroup J ℂ := (star V).2
  have hWs : Wᴴ = kronecker (U : Matrix I I ℂ)ᴴ (V : Matrix J J ℂ)ᴴ := by
    simp only [W, kr_eq, conjTranspose_kronecker]
  refine le_antisymm ?_ ?_
  · refine le_sInf ?_
    rintro _ ⟨σ, hσ, rfl⟩
    rw [← maxRel_conj hW rho σ]
    exact emax_le (sep_conj U.2 V.2 hσ)
  · refine le_sInf ?_
    rintro _ ⟨σ, hσ, rfl⟩
    have hWs' : Wᴴ ∈ unitaryGroup (I × J) ℂ := by rw [hWs]; exact kron_unit hU' hV'
    rw [← maxRel_conj hWs' (W * rho * Wᴴ) σ]
    have e : Wᴴ * (W * rho * Wᴴ) * Wᴴᴴ = rho := by
      rw [conjTranspose_conjTranspose]
      simp only [← Matrix.mul_assoc, unit_mul hW, Matrix.one_mul]
      rw [Matrix.mul_assoc, unit_mul hW, Matrix.mul_one]
    rw [e]
    refine emax_le ?_
    have := sep_conj hU' hV' hσ
    rw [← hWs] at this; exact this

end Bip
end X5G
end X5mod_G_Simple

section X5mod_G_Cone
open Matrix Set Filter Topology
open scoped ComplexOrder Kronecker

namespace X5G
open QAlgorithms.Entanglement (IsSeparableDensity)
open X5L13

section Cone
variable {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

def Gen (I J : Type) [Fintype I] [Fintype J] : Set (Matrix (I × J) (I × J) ℂ) :=
  {X | ∃ P : Matrix I I ℂ, ∃ Q : Matrix J J ℂ, P.PosSemidef ∧ Q.PosSemidef ∧ X = P ⊗ₖ Q}

/-- the cone generated by product positive operators -/
def SP (X : Matrix (I × J) (I × J) ℂ) : Prop := X ∈ AddSubmonoid.closure (Gen I J)

lemma sp_psd {X : Matrix (I × J) (I × J) ℂ} (h : SP X) : X.PosSemidef := by
  induction h using AddSubmonoid.closure_induction with
  | mem x hx =>
    obtain ⟨P, Q, hP, hQ, rfl⟩ := hx
    exact hP.kronecker hQ
  | zero => exact PosSemidef.zero
  | add x y _ _ hx hy => exact hx.add hy

lemma sp_add {X Y : Matrix (I × J) (I × J) ℂ} (hX : SP X) (hY : SP Y) : SP (X + Y) :=
  AddSubmonoid.add_mem _ hX hY

lemma sp_zero : SP (0 : Matrix (I × J) (I × J) ℂ) := AddSubmonoid.zero_mem _

lemma sp_sum {ι : Type} (s : Finset ι) (f : ι → Matrix (I × J) (I × J) ℂ) (h : ∀ i ∈ s, SP (f i)) :
    SP (∑ i ∈ s, f i) := AddSubmonoid.sum_mem _ h

lemma sp_list_sum (l : List (Matrix (I × J) (I × J) ℂ)) (h : ∀ x ∈ l, SP x) : SP l.sum :=
  AddSubmonoid.list_sum_mem _ h

lemma sp_smul {c : ℝ} (hc : 0 ≤ c) {X : Matrix (I × J) (I × J) ℂ} (h : SP X) : SP ((c : ℂ) • X) := by
  induction h using AddSubmonoid.closure_induction with
  | mem x hx =>
    obtain ⟨P, Q, hP, hQ, rfl⟩ := hx
    refine AddSubmonoid.subset_closure ⟨(c : ℂ) • P, Q, hP.smul (by exact_mod_cast hc), hQ, ?_⟩
    rw [Matrix.smul_kronecker]
  | zero => rw [smul_zero]; exact sp_zero
  | add x y _ _ hx hy => rw [smul_add]; exact sp_add hx hy

lemma sp_map {I' J' : Type} [Fintype I'] [DecidableEq I'] [Fintype J'] [DecidableEq J']
    (Φ : Matrix (I × J) (I × J) ℂ →+ Matrix (I' × J') (I' × J') ℂ)
    (hΦ : ∀ P Q, P.PosSemidef → Q.PosSemidef → SP (Φ (P ⊗ₖ Q)))
    {X : Matrix (I × J) (I × J) ℂ} (h : SP X) : SP (Φ X) := by
  induction h using AddSubmonoid.closure_induction with
  | mem x hx =>
    obtain ⟨P, Q, hP, hQ, rfl⟩ := hx
    exact hΦ P Q hP hQ
  | zero => rw [map_zero]; exact sp_zero
  | add x y _ _ hx hy => rw [map_add]; exact sp_add hx hy

/-- conjugation by a (possibly rectangular) operator -/
def conjHom {I' J' : Type} [Fintype I'] [Fintype J'] (L : Matrix (I' × J') (I × J) ℂ) :
    Matrix (I × J) (I × J) ℂ →+ Matrix (I' × J') (I' × J') ℂ where
  toFun X := L * X * Lᴴ
  map_zero' := by simp
  map_add' X Y := by rw [Matrix.mul_add, Matrix.add_mul]

lemma sp_conj {I' J' : Type} [Fintype I'] [DecidableEq I'] [Fintype J'] [DecidableEq J']
    (M : Matrix I' I ℂ) (N : Matrix J' J ℂ) {X : Matrix (I × J) (I × J) ℂ} (h : SP X) :
    SP ((M ⊗ₖ N) * X * (M ⊗ₖ N)ᴴ) := by
  refine sp_map (conjHom (M ⊗ₖ N)) (fun P Q hP hQ => ?_) h
  show SP ((M ⊗ₖ N) * (P ⊗ₖ Q) * (M ⊗ₖ N)ᴴ)
  rw [conjTranspose_kronecker, ← mul_kronecker_mul, ← mul_kronecker_mul]
  exact AddSubmonoid.subset_closure ⟨_, _, hP.mul_mul_conjTranspose_same M,
    hQ.mul_mul_conjTranspose_same N, rfl⟩

/-- reindexing by a product of equivalences -/
def subHom {I' J' : Type} (e : I' ≃ I) (f : J' ≃ J) :
    Matrix (I × J) (I × J) ℂ →+ Matrix (I' × J') (I' × J') ℂ where
  toFun X := X.submatrix (Prod.map e f) (Prod.map e f)
  map_zero' := by ext; simp
  map_add' X Y := by ext; simp

lemma sp_sub {I' J' : Type} [Fintype I'] [DecidableEq I'] [Fintype J'] [DecidableEq J']
    (e : I' ≃ I) (f : J' ≃ J) {X : Matrix (I × J) (I × J) ℂ} (h : SP X) :
    SP (X.submatrix (Prod.map e f) (Prod.map e f)) := by
  refine sp_map (subHom e f) (fun P Q hP hQ => ?_) h
  show SP ((P ⊗ₖ Q).submatrix (Prod.map e f) (Prod.map e f))
  refine AddSubmonoid.subset_closure ⟨P.submatrix e e, Q.submatrix f f,
    (posSemidef_submatrix_equiv e).mpr hP, (posSemidef_submatrix_equiv f).mpr hQ, ?_⟩
  ext a b; simp [Matrix.kroneckerMap_apply]

variable [Nonempty I] [Nonempty J]

lemma sp_of_sep {X : Matrix (I × J) (I × J) ℂ} (h : IsSeparableDensity X) : SP X := by
  obtain ⟨q, w, A, B, hw, hs, hd, rfl⟩ := h
  refine sp_sum _ _ fun j _ => ?_
  rw [kr_eq]
  refine AddSubmonoid.subset_closure ⟨(w j : ℂ) • A j, B j, (hd j).1.1.smul (by exact_mod_cast hw j),
    (hd j).2.1, ?_⟩
  rw [Matrix.smul_kronecker]

/-- normalization of a positive operator -/
lemma normalize {K : Type} [Fintype K] [DecidableEq K] [Nonempty K] {P : Matrix K K ℂ}
    (hP : P.PosSemidef) : ∃ A : Matrix K K ℂ, QAlgorithms.IsDensityMatrix A ∧
      P = ((P.trace.re : ℝ) : ℂ) • A := by
  by_cases h0 : P.trace.re = 0
  · have htr : P.trace = 0 := by
      have him : P.trace.im = 0 := (Complex.nonneg_iff.mp hP.trace_nonneg).2.symm
      exact Complex.ext h0 him
    have hP0 : P = 0 := hP.trace_eq_zero_iff.mp htr
    obtain ⟨A, hA⟩ := X5L13.dens_ex K
    exact ⟨A, hA, by rw [hP0]; simp⟩
  · have hpos : 0 < P.trace.re := lt_of_le_of_ne (psd_re hP) (Ne.symm h0)
    have htr : P.trace = ((P.trace.re : ℝ) : ℂ) := by
      have him : P.trace.im = 0 := (Complex.nonneg_iff.mp hP.trace_nonneg).2.symm
      exact Complex.ext (by simp) (by simp [him])
    refine ⟨((P.trace.re : ℝ) : ℂ)⁻¹ • P, ⟨hP.smul ?_, ?_⟩, ?_⟩
    · have : (0 : ℝ) ≤ (P.trace.re)⁻¹ := (inv_pos.mpr hpos).le
      exact_mod_cast this
    · rw [Matrix.trace_smul, smul_eq_mul]
      have : ((P.trace.re : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
      conv_lhs => rw [htr]
      rw [Complex.ofReal_re, inv_mul_cancel₀ this]
    · rw [smul_smul]
      have : ((P.trace.re : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
      rw [mul_inv_cancel₀ this, one_smul]

lemma sp_fin {X : Matrix (I × J) (I × J) ℂ} (h : SP X) :
    ∃ q : ℕ, ∃ P : Fin q → Matrix I I ℂ, ∃ Q : Fin q → Matrix J J ℂ,
      (∀ j, (P j).PosSemidef ∧ (Q j).PosSemidef) ∧ X = ∑ j, P j ⊗ₖ Q j := by
  induction h using AddSubmonoid.closure_induction with
  | mem x hx =>
    obtain ⟨P, Q, hP, hQ, rfl⟩ := hx
    exact ⟨1, fun _ => P, fun _ => Q, fun _ => ⟨hP, hQ⟩, by simp⟩
  | zero => exact ⟨0, Fin.elim0, Fin.elim0, fun j => Fin.elim0 j, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, P1, Q1, h1, rfl⟩ := hx
    obtain ⟨b, P2, Q2, h2, rfl⟩ := hy
    refine ⟨a + b, Fin.append P1 P2, Fin.append Q1 Q2, fun j => ?_, ?_⟩
    · refine Fin.addCases (fun i => ?_) (fun i => ?_) j
      · simp only [Fin.append_left]; exact h1 i
      · simp only [Fin.append_right]; exact h2 i
    · rw [Fin.sum_univ_add]; simp only [Fin.append_left, Fin.append_right]

lemma sep_of_sp {X : Matrix (I × J) (I × J) ℂ} (h : SP X) (htr : X.trace = 1) :
    IsSeparableDensity X := by
  obtain ⟨q, P, Q, hPQ, rfl⟩ := sp_fin h
  choose A hA eA using fun j => normalize (hPQ j).1
  choose B hB eB using fun j => normalize (hPQ j).2
  set w : Fin q → ℝ := fun j => (P j).trace.re * (Q j).trace.re
  have hw : ∀ j, 0 ≤ w j := fun j => mul_nonneg (psd_re (hPQ j).1) (psd_re (hPQ j).2)
  have e : ∀ j, P j ⊗ₖ Q j = ((w j : ℝ) : ℂ) • kronecker (A j) (B j) := by
    intro j
    conv_lhs => rw [eA j, eB j]
    rw [Matrix.smul_kronecker, Matrix.kronecker_smul, smul_smul, kr_eq]
    simp only [w, Complex.ofReal_mul]
  simp only [e] at htr ⊢
  refine ⟨q, w, A, B, hw, ?_, fun j => ⟨hA j, hB j⟩, rfl⟩
  rw [Matrix.trace_sum] at htr
  have ht : ∀ j, (((w j : ℝ) : ℂ) • kronecker (A j) (B j)).trace = ((w j : ℝ) : ℂ) := by
    intro j
    rw [Matrix.trace_smul, kr_eq, Matrix.trace_kronecker, (hA j).2, (hB j).2]; simp
  simp only [ht] at htr
  exact_mod_cast htr

end Cone
end X5G
end X5mod_G_Cone

section X5mod_G_Bund
open Matrix Set Filter Topology
open scoped ComplexOrder Kronecker

namespace X5G
open QAlgorithms.Entanglement (IsSeparableDensity)
open QAlgorithms.Papers.Independent.Dependency50.P35 (tr maxRelative)
open QAlgorithms.Papers.Independent.Support50.P21 (eMax bundledMatrix bundledEMax)
open QAlgorithms.Papers.Independent.Claimed50.P33
  (FiniteState RegisterBasis stateEntry LocalInstrument liftLocalKraus LOCC)
open X5L13

abbrev Sp (d : Fin 2 → ℕ) := Fin (d 0) × Fin (d 1)

def eb (d : Fin 2 → ℕ) : Sp d ≃ RegisterBasis (fun i => Fin (d i)) where
  toFun x := Fin.cases x.1 (Fin.cases x.2 (fun i => Fin.elim0 i))
  invFun f := (f 0, f 1)
  left_inv x := rfl
  right_inv f := by funext i; fin_cases i <;> rfl

@[simp] lemma eb0 (d : Fin 2 → ℕ) (x : Sp d) : eb d x 0 = x.1 := rfl
@[simp] lemma eb1 (d : Fin 2 → ℕ) (x : Sp d) : eb d x 1 = x.2 := rfl

lemma bm_eq (s : FiniteState 2) : bundledMatrix s = s.rho.submatrix (eb s.dims) (eb s.dims) := rfl

lemma sub_sum {m n m' n' ι : Type} (S : Finset ι) (f : ι → Matrix m n ℂ) (r : m' → m) (c : n' → n) :
    (∑ i ∈ S, f i).submatrix r c = ∑ i ∈ S, (f i).submatrix r c := by
  ext a b; simp [Matrix.sum_apply]

lemma tr_sub_equiv {m n : Type} [Fintype m] [Fintype n] (e : m ≃ n) (M : Matrix n n ℂ) :
    (M.submatrix e e).trace = M.trace := by
  unfold Matrix.trace; simp only [Matrix.diag_apply, Matrix.submatrix_apply]
  exact Equiv.sum_comp e (fun i => M i i)

lemma bm_dens (s : FiniteState 2) : QAlgorithms.IsDensityMatrix (bundledMatrix s) := by
  rw [bm_eq]
  exact ⟨(posSemidef_submatrix_equiv _).mpr s.normalized.1, by rw [tr_sub_equiv, s.normalized.2]⟩

instance ne0 (s : FiniteState 2) : Nonempty (Fin (s.dims 0)) := ⟨⟨0, s.positive 0⟩⟩
instance ne1 (s : FiniteState 2) : Nonempty (Fin (s.dims 1)) := ⟨⟨0, s.positive 1⟩⟩

lemma g_spec (s : FiniteState 2) : ∃ σ : Matrix (Sp s.dims) (Sp s.dims) ℂ, IsSeparableDensity σ ∧
    Feas (bundledMatrix s) σ (bundledEMax s) ∧ 0 ≤ bundledEMax s ∧
    eMax (bundledMatrix s) = ((bundledEMax s : ℝ) : EReal) := by
  obtain ⟨z, hz0, hz, σ, hσ, hF, -⟩ := attain (bm_dens s)
  have hg : bundledEMax s = z := by
    unfold bundledEMax; rw [hz]; rfl
  rw [hg]; exact ⟨σ, hσ, hF, hz0, hz⟩

lemma H1 (s : FiniteState 2) {p : ℝ} (hp : 0 ≤ p) {τ : Matrix (Sp s.dims) (Sp s.dims) ℂ} (hτ : SP τ)
    (hle : (τ - (p : ℂ) • bundledMatrix s).PosSemidef) :
    p * (2 : ℝ) ^ bundledEMax s ≤ τ.trace.re := by
  have hρ := bm_dens s
  set c := τ.trace.re
  have hc : p ≤ c := by
    have := psd_re hle
    rw [Matrix.trace_sub, Matrix.trace_smul, hρ.2] at this
    simpa using this
  rcases hp.eq_or_lt with h0 | hpos
  · rw [← h0, zero_mul]; exact psd_re (sp_psd hτ)
  · have hc0 : 0 < c := lt_of_lt_of_le hpos hc
    set σ := ((c⁻¹ : ℝ) : ℂ) • τ
    have hσ : IsSeparableDensity σ := by
      refine sep_of_sp (sp_smul (inv_pos.mpr hc0).le hτ) ?_
      have htr : τ.trace = (c : ℂ) := by
        have him : τ.trace.im = 0 := (Complex.nonneg_iff.mp (sp_psd hτ).trace_nonneg).2.symm
        exact Complex.ext (by simp [c]) (by simp [him])
      rw [Matrix.trace_smul, htr, smul_eq_mul, ← Complex.ofReal_mul, inv_mul_cancel₀ hc0.ne']; simp
    have hF : Feas (bundledMatrix s) σ (Real.logb 2 (c / p)) := by
      unfold Feas
      rw [Real.rpow_logb (by norm_num) (by norm_num) (div_pos hc0 hpos)]
      have e : (((c / p : ℝ)) : ℂ) • σ - bundledMatrix s = ((p⁻¹ : ℝ) : ℂ) • (τ - (p : ℂ) • bundledMatrix s) := by
        simp only [σ, smul_smul, smul_sub, ← Complex.ofReal_mul]
        rw [show c / p * c⁻¹ = p⁻¹ by field_simp, show p⁻¹ * p = 1 by field_simp]
        simp
      rw [e]; exact hle.smul (by exact_mod_cast (inv_pos.mpr hpos).le)
    obtain ⟨-, -, -, -, hz⟩ := g_spec s
    have hle2 : ((bundledEMax s : ℝ) : EReal) ≤ ((Real.logb 2 (c / p) : ℝ) : EReal) :=
      hz ▸ (emax_le hσ).trans (maxRel_le hF)
    have hle3 : bundledEMax s ≤ Real.logb 2 (c / p) := EReal.coe_le_coe_iff.mp hle2
    have h4 : (2 : ℝ) ^ bundledEMax s ≤ c / p := by
      calc (2 : ℝ) ^ bundledEMax s ≤ (2 : ℝ) ^ Real.logb 2 (c / p) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) hle3
        _ = c / p := Real.rpow_logb (by norm_num) (by norm_num) (div_pos hc0 hpos)
    rw [le_div_iff₀ hpos] at h4
    linarith

lemma H2 (s : FiniteState 2) {p : ℝ} (hp : 0 ≤ p) : ∃ τ : Matrix (Sp s.dims) (Sp s.dims) ℂ, SP τ ∧
    (τ - (p : ℂ) • bundledMatrix s).PosSemidef ∧ τ.trace.re = p * (2 : ℝ) ^ bundledEMax s := by
  obtain ⟨σ, hσ, hF, -, -⟩ := g_spec s
  refine ⟨((p * (2 : ℝ) ^ bundledEMax s : ℝ) : ℂ) • σ, sp_smul (by positivity) (sp_of_sep hσ), ?_, ?_⟩
  · have e : ((p * (2 : ℝ) ^ bundledEMax s : ℝ) : ℂ) • σ - (p : ℂ) • bundledMatrix s =
        (p : ℂ) • ((((2 : ℝ) ^ bundledEMax s : ℝ) : ℂ) • σ - bundledMatrix s) := by
      rw [smul_sub, smul_smul, ← Complex.ofReal_mul]
    rw [e]; exact hF.smul (by exact_mod_cast hp)
  · rw [Matrix.trace_smul, (sep_dens hσ).2]; simp

end X5G
end X5mod_G_Bund

section X5mod_G_Inst
open Matrix Set Filter Topology
open scoped ComplexOrder Kronecker

namespace X5G
open QAlgorithms.Entanglement (IsSeparableDensity)
open QAlgorithms.Papers.Independent.Support50.P21 (eMax bundledMatrix bundledEMax)
open QAlgorithms.Papers.Independent.Claimed50.P33
  (FiniteState RegisterBasis stateEntry LocalInstrument liftLocalKraus LOCC)
open X5L13

/-- the identity between registers of equal size, as a rectangular matrix -/
def Ec (m n : ℕ) : Matrix (Fin m) (Fin n) ℂ := fun x y => if x.val = y.val then 1 else 0

lemma lift_form (s t : FiniteState 2) (party : Fin 2)
    (A : Matrix (Fin (t.dims party)) (Fin (s.dims party)) ℂ) :
    ∃ M : Matrix (Fin (t.dims 0)) (Fin (s.dims 0)) ℂ, ∃ N : Matrix (Fin (t.dims 1)) (Fin (s.dims 1)) ℂ,
      (liftLocalKraus s t party A).submatrix (eb t.dims) (eb s.dims) = M ⊗ₖ N := by
  obtain rfl | rfl : party = 0 ∨ party = 1 := by fin_cases party <;> simp
  · refine ⟨A, Ec _ _, ?_⟩
    ext ⟨a0, a1⟩ ⟨b0, b1⟩
    simp only [Matrix.submatrix_apply, liftLocalKraus, Matrix.kroneckerMap_apply, Ec]
    have h1 : (∀ i : Fin 2, i ≠ 0 → ((eb t.dims (a0, a1)) i).val = ((eb s.dims (b0, b1)) i).val) ↔
        a1.val = b1.val := by
      rw [Fin.forall_fin_two]; simp
    rw [if_congr h1 rfl rfl]
    split_ifs <;> simp
  · refine ⟨Ec _ _, A, ?_⟩
    ext ⟨a0, a1⟩ ⟨b0, b1⟩
    simp only [Matrix.submatrix_apply, liftLocalKraus, Matrix.kroneckerMap_apply, Ec]
    have h1 : (∀ i : Fin 2, i ≠ 1 → ((eb t.dims (a0, a1)) i).val = ((eb s.dims (b0, b1)) i).val) ↔
        a0.val = b0.val := by
      rw [Fin.forall_fin_two]; simp
    rw [if_congr h1 rfl rfl]
    split_ifs <;> simp

theorem LI {s : FiniteState 2} {k : ℕ} {p : Fin k → ℝ} {r : Fin k → FiniteState 2}
    (h : LocalInstrument s p r) {τ : Matrix (Sp s.dims) (Sp s.dims) ℂ} (hτ : SP τ)
    (hle : (τ - bundledMatrix s).PosSemidef) :
    ∃ τj : (j : Fin k) → Matrix (Sp (r j).dims) (Sp (r j).dims) ℂ,
      (∀ j, SP (τj j) ∧ (τj j - (p j : ℂ) • bundledMatrix (r j)).PosSemidef) ∧
      ∑ j, (τj j).trace.re = τ.trace.re := by
  obtain ⟨-, -, party, count, A, -, hcomp, heq⟩ := h
  set Lb : (j : Fin k) → Fin (count j) → Matrix (Sp (r j).dims) (Sp s.dims) ℂ :=
    fun j z => (liftLocalKraus s (r j) party (A j z)).submatrix (eb (r j).dims) (eb s.dims)
  refine ⟨fun j => ∑ z, Lb j z * τ * (Lb j z)ᴴ, fun j => ⟨?_, ?_⟩, ?_⟩
  · refine sp_sum _ _ fun z _ => ?_
    obtain ⟨M, N, hMN⟩ := lift_form s (r j) party (A j z)
    show SP ((liftLocalKraus s (r j) party (A j z)).submatrix (eb (r j).dims) (eb s.dims) * τ *
      ((liftLocalKraus s (r j) party (A j z)).submatrix (eb (r j).dims) (eb s.dims))ᴴ)
    rw [hMN]; exact sp_conj M N hτ
  · have hb : (p j : ℂ) • bundledMatrix (r j) = ∑ z, Lb j z * bundledMatrix s * (Lb j z)ᴴ := by
      have key : ((p j : ℂ) • (r j).rho).submatrix (eb (r j).dims) (eb (r j).dims) =
          (p j : ℂ) • (r j).rho.submatrix (eb (r j).dims) (eb (r j).dims) := by ext; simp
      rw [bm_eq, bm_eq, ← key, heq j, sub_sum]
      refine Finset.sum_congr rfl fun z _ => ?_
      simp only [Lb, conjTranspose_submatrix, submatrix_mul_equiv]
    rw [hb, ← Finset.sum_sub_distrib]
    refine Matrix.posSemidef_sum _ fun z _ => ?_
    rw [← Matrix.sub_mul, ← Matrix.mul_sub]
    exact hle.mul_mul_conjTranspose_same _
  · have hc : ∑ j, ∑ z, (Lb j z)ᴴ * Lb j z = 1 := by
      have := congrArg (fun X => X.submatrix (eb s.dims) (eb s.dims)) hcomp
      simp only [sub_sum, submatrix_one_equiv] at this
      rw [← this]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun z _ => ?_
      simp only [Lb, conjTranspose_submatrix, submatrix_mul_equiv]
    have e : ∀ j, (∑ z, Lb j z * τ * (Lb j z)ᴴ).trace = (∑ z, (Lb j z)ᴴ * Lb j z * τ).trace := by
      intro j
      rw [Matrix.trace_sum, Matrix.trace_sum]
      refine Finset.sum_congr rfl fun z _ => ?_
      rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc]
    simp only [e]
    rw [← Complex.re_sum, ← Matrix.trace_sum]
    simp only [← Finset.sum_mul]
    rw [hc, Matrix.one_mul]

end X5G
end X5mod_G_Inst

section X5mod_G_LOCC
open Matrix Set Filter Topology
open scoped ComplexOrder Kronecker

namespace X5G
open QAlgorithms.Entanglement (IsSeparableDensity)
open QAlgorithms.Papers.Independent.Support50.P21 (eMax bundledMatrix bundledEMax)
open QAlgorithms.Papers.Independent.Claimed50.P33
  (FiniteState RegisterBasis stateEntry LocalInstrument liftLocalKraus LOCC
   IsAverageLocalMonotone IsAdaptiveLOCCMonotone)
open X5L13

/-- the local-instrument inequality for `2 ^ Emax` -/
theorem inst_le {s : FiniteState 2} {k : ℕ} {p : Fin k → ℝ} {r : Fin k → FiniteState 2}
    (h : LocalInstrument s p r) :
    ∑ j, p j * (2 : ℝ) ^ bundledEMax (r j) ≤ (2 : ℝ) ^ bundledEMax s := by
  obtain ⟨τ, hτ, hle, htr⟩ := H2 s (p := 1) zero_le_one
  rw [Complex.ofReal_one, one_smul] at hle
  obtain ⟨τj, hj, hsum⟩ := LI h hτ hle
  rw [htr, one_mul] at hsum
  rw [← hsum]
  exact Finset.sum_le_sum fun j _ => H1 (r j) (h.1 j) (hj j).1 (hj j).2

lemma list_flatMap_sum {α β : Type} (L : List α) (F : α → List β) (f : β → ℝ) :
    ((L.flatMap F).map f).sum = (L.map fun a => ((F a).map f).sum).sum := by
  induction L with
  | nil => simp
  | cons a L ih => simp [List.flatMap_cons, ih]

lemma finRange_sum {k : ℕ} (f : Fin k → ℝ) : ((List.finRange k).map f).sum = ∑ j, f j :=
  (Fin.sum_univ_def f).symm

/-- the transport of a matrix between equal-dimensional bundled spaces -/
def ec {d e : Fin 2 → ℕ} (h : e = d) : Sp d ≃ Sp e :=
  (finCongr (congrFun h 0).symm).prodCongr (finCongr (congrFun h 1).symm)

def TT (t u : FiniteState 2) (M : Matrix (Sp u.dims) (Sp u.dims) ℂ) : Matrix (Sp t.dims) (Sp t.dims) ℂ :=
  if h : u.dims = t.dims then M.submatrix (Prod.map (finCongr (congrFun h 0).symm) (finCongr (congrFun h 1).symm))
    (Prod.map (finCongr (congrFun h 0).symm) (finCongr (congrFun h 1).symm)) else 0

lemma TT_sub (t u : FiniteState 2) (M N : Matrix (Sp u.dims) (Sp u.dims) ℂ) :
    TT t u M - TT t u N = TT t u (M - N) := by
  unfold TT; split_ifs <;> ext <;> simp

lemma TT_smul (t u : FiniteState 2) (c : ℂ) (M : Matrix (Sp u.dims) (Sp u.dims) ℂ) :
    c • TT t u M = TT t u (c • M) := by
  unfold TT; split_ifs <;> ext <;> simp

lemma TT_psd (t u : FiniteState 2) (h : u.dims = t.dims) {M : Matrix (Sp u.dims) (Sp u.dims) ℂ}
    (hM : M.PosSemidef) : (TT t u M).PosSemidef := by
  unfold TT; rw [dif_pos h]; exact hM.submatrix _

lemma TT_sp (t u : FiniteState 2) (h : u.dims = t.dims) {M : Matrix (Sp u.dims) (Sp u.dims) ℂ}
    (hM : SP M) : SP (TT t u M) := by
  unfold TT; rw [dif_pos h]; exact sp_sub _ _ hM

lemma TT_tr (t u : FiniteState 2) (h : u.dims = t.dims) (M : Matrix (Sp u.dims) (Sp u.dims) ℂ) :
    (TT t u M).trace = M.trace := by
  unfold TT; rw [dif_pos h]
  exact tr_sub_equiv ((finCongr (congrFun h 0).symm).prodCongr (finCongr (congrFun h 1).symm)) M

lemma list_psd {K : Type} [Fintype K] (l : List (Matrix K K ℂ)) (h : ∀ x ∈ l, x.PosSemidef) :
    l.sum.PosSemidef := by
  induction l with
  | nil => exact PosSemidef.zero
  | cons a l ih =>
    rw [List.sum_cons]
    exact (h a (List.mem_cons_self ..)).add (ih fun x hx => h x (List.mem_cons_of_mem _ hx))

lemma list_apply {K : Type} {β : Type} (l : List β) (F : β → Matrix K K ℂ) (a b : K) :
    (l.map F).sum a b = (l.map fun w => F w a b).sum := by
  induction l with
  | nil => simp
  | cons x l ih => simp [ih]

lemma list_re {β : Type} (l : List β) (F : β → ℂ) : (l.map F).sum.re = (l.map fun w => (F w).re).sum := by
  induction l with
  | nil => simp
  | cons x l ih => simp [ih]

lemma list_trace {K : Type} [Fintype K] {β : Type} (l : List β) (F : β → Matrix K K ℂ) :
    (l.map F).sum.trace = (l.map fun w => (F w).trace).sum := by
  induction l with
  | nil => simp
  | cons x l ih => simp [ih, Matrix.trace_add]

lemma list_sub {K : Type} {β : Type} (l : List β) (F G : β → Matrix K K ℂ) :
    (l.map F).sum - (l.map G).sum = (l.map fun w => F w - G w).sum := by
  induction l with
  | nil => simp
  | cons x l ih => simp only [List.map_cons, List.sum_cons]; rw [← ih]; abel

lemma bm_entry (t : FiniteState 2) (a b : Sp t.dims) :
    bundledMatrix t a b = stateEntry t (fun i => (eb t.dims a i).val) (fun i => (eb t.dims b i).val) := by
  unfold stateEntry
  rw [dif_pos ⟨fun i => (eb t.dims a i).isLt, fun i => (eb t.dims b i).isLt⟩]
  rfl

lemma TT_entry (t u : FiniteState 2) (h : u.dims = t.dims) (a b : Sp t.dims) :
    TT t u (bundledMatrix u) a b =
      stateEntry u (fun i => (eb t.dims a i).val) (fun i => (eb t.dims b i).val) := by
  unfold stateEntry TT
  have hlt : ∀ (c : Sp t.dims) i, (eb t.dims c i).val < u.dims i := fun c i => by
    rw [h]; exact (eb t.dims c i).isLt
  rw [dif_pos h, dif_pos ⟨hlt a, hlt b⟩]
  simp only [Matrix.submatrix_apply, bm_eq]
  congr 1 <;> (funext i; fin_cases i <;> rfl)

noncomputable def sigStar (u : FiniteState 2) : Matrix (Sp u.dims) (Sp u.dims) ℂ :=
  Classical.choose (g_spec u)

lemma sigStar_spec (u : FiniteState 2) : IsSeparableDensity (sigStar u) ∧
    Feas (bundledMatrix u) (sigStar u) (bundledEMax u) := by
  have := Classical.choose_spec (g_spec u)
  exact ⟨this.1, this.2.1⟩

/-- the transported inequality for the transcript-forgetting step -/
theorem forget_le (t : FiniteState 2) (out : List (ℝ × FiniteState 2))
    (hd : ∀ w ∈ out, w.2.dims = t.dims) (hnn : ∀ w ∈ out, 0 ≤ w.1)
    (hmix : ∀ x y, stateEntry t x y = (out.map fun w => (w.1 : ℂ) * stateEntry w.2 x y).sum) :
    (2 : ℝ) ^ bundledEMax t ≤ (out.map fun w => w.1 * (2 : ℝ) ^ bundledEMax w.2).sum := by
  set τw : (w : ℝ × FiniteState 2) → Matrix (Sp t.dims) (Sp t.dims) ℂ := fun w =>
    TT t w.2 (((w.1 * (2 : ℝ) ^ bundledEMax w.2 : ℝ) : ℂ) • sigStar w.2)
  set τ := (out.map τw).sum
  have hbm : bundledMatrix t = (out.map fun w => (w.1 : ℂ) • TT t w.2 (bundledMatrix w.2)).sum := by
    ext a b
    rw [bm_entry, hmix, list_apply]
    refine congrArg List.sum (List.map_congr_left fun w hw => ?_)
    rw [Matrix.smul_apply, TT_entry t w.2 (hd w hw), smul_eq_mul]
  have hsp : SP τ := sp_list_sum _ (by
    intro x hx
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hx
    exact TT_sp t w.2 (hd w hw) (sp_smul (mul_nonneg (hnn w hw) (by positivity))
      (sp_of_sep (sigStar_spec w.2).1)))
  have hle : (τ - ((1 : ℝ) : ℂ) • bundledMatrix t).PosSemidef := by
    rw [Complex.ofReal_one, one_smul, hbm, list_sub]
    refine list_psd _ fun x hx => ?_
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hx
    simp only [τw]
    rw [TT_smul, TT_sub]
    refine TT_psd t w.2 (hd w hw) ?_
    have e : ((w.1 * (2 : ℝ) ^ bundledEMax w.2 : ℝ) : ℂ) • sigStar w.2 - (w.1 : ℂ) • bundledMatrix w.2 =
        (w.1 : ℂ) • ((((2 : ℝ) ^ bundledEMax w.2 : ℝ) : ℂ) • sigStar w.2 - bundledMatrix w.2) := by
      rw [smul_sub, smul_smul, ← Complex.ofReal_mul]
    rw [e]; exact (sigStar_spec w.2).2.smul (by exact_mod_cast hnn w hw)
  have h1 := H1 t zero_le_one hsp hle
  rw [one_mul] at h1
  refine h1.trans (le_of_eq ?_)
  rw [list_trace, list_re]
  refine congrArg List.sum (List.map_congr_left fun w hw => ?_)
  simp only [τw]
  rw [TT_tr t w.2 (hd w hw), Matrix.trace_smul, (sep_dens (sigStar_spec w.2).1).2]
  simp

/-- the induction invariant over adaptive LOCC trees -/
theorem inv {s : FiniteState 2} {out : List (ℝ × FiniteState 2)} (h : LOCC s out) :
    (∀ w ∈ out, 0 ≤ w.1) ∧ (out.map fun w => w.1).sum = 1 ∧
      (out.map fun w => w.1 * (2 : ℝ) ^ bundledEMax w.2).sum ≤ (2 : ℝ) ^ bundledEMax s := by
  induction h with
  | stop s => simp
  | step s k p r hI next hn ih =>
    refine ⟨?_, ?_, ?_⟩
    · intro w hw
      obtain ⟨j, -, hj⟩ := List.mem_flatMap.mp hw
      obtain ⟨w', hw', rfl⟩ := List.mem_map.mp hj
      exact mul_nonneg (hI.1 j) ((ih j).1 w' hw')
    · rw [list_flatMap_sum, finRange_sum]
      simp only [List.map_map, Function.comp_def]
      rw [← hI.2.1]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [List.sum_map_mul_left, (ih j).2.1, mul_one]
    · rw [list_flatMap_sum, finRange_sum]
      simp only [List.map_map, Function.comp_def]
      refine le_trans ?_ (inst_le hI)
      refine Finset.sum_le_sum fun j _ => ?_
      have e : ((next j).map fun x => p j * x.1 * (2 : ℝ) ^ bundledEMax x.2).sum =
          p j * ((next j).map fun x => x.1 * (2 : ℝ) ^ bundledEMax x.2).sum := by
        rw [← List.sum_map_mul_left]; simp only [mul_assoc]
      rw [e]
      exact mul_le_mul_of_nonneg_left (ih j).2.2 (hI.1 j)
  | forget s t out h hd hmix ih =>
    refine ⟨by simp, by simp, ?_⟩
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, one_mul]
    exact (forget_le t out hd ih.1 hmix).trans ih.2.2

lemma tangent {a x y : ℝ} (ha : 0 ≤ a) :
    Real.log 2 * (a * x) ≤ Real.log 2 * y * a + a * (2 : ℝ) ^ x * (2 : ℝ) ^ (-y) - a := by
  have h := Real.add_one_le_exp ((x - y) * Real.log 2)
  have e : Real.exp ((x - y) * Real.log 2) = (2 : ℝ) ^ x * (2 : ℝ) ^ (-y) := by
    rw [← Real.rpow_add (by norm_num), mul_comm, Real.rpow_def_of_pos (by norm_num)]
    ring_nf
  rw [e] at h
  nlinarith [mul_le_mul_of_nonneg_left h ha]

lemma list_tangent (l : List (ℝ × FiniteState 2)) (y : ℝ) (hnn : ∀ w ∈ l, 0 ≤ w.1) :
    Real.log 2 * (l.map fun w => w.1 * bundledEMax w.2).sum ≤
      Real.log 2 * y * (l.map fun w => w.1).sum +
        (l.map fun w => w.1 * (2 : ℝ) ^ bundledEMax w.2).sum * (2 : ℝ) ^ (-y) -
        (l.map fun w => w.1).sum := by
  induction l with
  | nil => simp
  | cons w l ih =>
    have h1 := tangent (x := bundledEMax w.2) (y := y) (hnn w (List.mem_cons_self ..))
    have h2 := ih fun x hx => hnn x (List.mem_cons_of_mem _ hx)
    simp only [List.map_cons, List.sum_cons]
    nlinarith

theorem adaptive : IsAdaptiveLOCCMonotone bundledEMax := by
  intro s out h
  obtain ⟨hnn, hs, hle⟩ := inv h
  have ht := list_tangent out (bundledEMax s) hnn
  rw [hs] at ht
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h3 : (out.map fun w => w.1 * (2 : ℝ) ^ bundledEMax w.2).sum * (2 : ℝ) ^ (-bundledEMax s) ≤ 1 := by
    calc _ ≤ (2 : ℝ) ^ bundledEMax s * (2 : ℝ) ^ (-bundledEMax s) :=
          mul_le_mul_of_nonneg_right hle (by positivity)
      _ = 1 := by rw [← Real.rpow_add (by norm_num), add_neg_cancel, Real.rpow_zero]
  have : Real.log 2 * (out.map fun w => w.1 * bundledEMax w.2).sum ≤ Real.log 2 * bundledEMax s := by
    nlinarith
  exact le_of_mul_le_mul_left this hl2

theorem average : IsAverageLocalMonotone bundledEMax := by
  intro s k p r h
  have hle := inst_le h
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set y := bundledEMax s
  have hpt : ∀ j, Real.log 2 * (p j * bundledEMax (r j)) ≤
      Real.log 2 * y * p j + p j * (2 : ℝ) ^ bundledEMax (r j) * (2 : ℝ) ^ (-y) - p j :=
    fun j => tangent (h.1 j)
  have hs := Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) => hpt j
  rw [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Finset.sum_mul, h.2.1] at hs
  have h3 : (∑ j, p j * (2 : ℝ) ^ bundledEMax (r j)) * (2 : ℝ) ^ (-y) ≤ 1 := by
    calc _ ≤ (2 : ℝ) ^ y * (2 : ℝ) ^ (-y) := mul_le_mul_of_nonneg_right hle (by positivity)
      _ = 1 := by rw [← Real.rpow_add (by norm_num), add_neg_cancel, Real.rpow_zero]
  have : Real.log 2 * ∑ j, p j * bundledEMax (r j) ≤ Real.log 2 * y := by nlinarith
  exact le_of_mul_le_mul_left this hl2

end X5G
end X5mod_G_LOCC

section X5mod_G_Main

end X5mod_G_Main

noncomputable section

open QAlgorithms QAlgorithms.Entanglement Filter

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Support50.P21
open QAlgorithms.Papers.Independent.Claimed50.P33
  (FiniteState IsAverageLocalMonotone IsAdaptiveLOCCMonotone)
open QAlgorithms.Papers.Independent.Information100.P63 (Mat)
open QAlgorithms.Papers.Independent.Dependency50.P35 (tr elog maxRelative)

section Statements

variable {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

variable [Nonempty I] [Nonempty J]

theorem solution :
    (∀ rho : Mat (I × J), IsDensityMatrix rho →
      ∃ z : ℝ, 0 ≤ z ∧ eMax rho = (z : EReal) ∧
        ∃ sigma : Mat (I × J), IsSeparableDensity sigma ∧ maxRelative rho sigma = eMax rho) ∧
    (∀ rho : Mat (I × J), IsDensityMatrix rho →
      (eMax rho = 0 ↔ IsSeparableDensity rho)) ∧
    (∀ (rho : Mat (I × J)), IsDensityMatrix rho →
      ∀ (U : Matrix.unitaryGroup I ℂ) (V : Matrix.unitaryGroup J ℂ),
      eMax (conjSuperop (Matrix.kronecker (U : Mat I) (V : Mat J)) rho) = eMax rho) ∧
    IsAverageLocalMonotone bundledEMax ∧ IsAdaptiveLOCCMonotone bundledEMax := by
  refine ⟨fun rho hrho => ?_, fun rho hrho => X5G.zero_iff hrho,
    fun rho _ U V => X5G.unitary_inv rho U V, X5G.average, X5G.adaptive⟩
  obtain ⟨z, hz0, hz, sigma, hs, -, he⟩ := X5G.attain hrho
  exact ⟨z, hz0, hz, sigma, hs, he⟩

end Statements

end
