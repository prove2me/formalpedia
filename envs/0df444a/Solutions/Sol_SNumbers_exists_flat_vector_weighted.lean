-- Prove2me | solution 1 for SNumbers.exists_flat_vector_weighted
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:15:42.043014+00:00
-- url     : https://prove2.me/submissions/f454bbd5-651d-40fb-9568-7c749b66e32d

module
public import Definitions.Def_SNumbers_Basic
public import Definitions.Def_SNumbers_PiLpCoordinates
public import Mathlib.Analysis.Convex.KreinMilman
public import Definitions.Def_SNumbers_Examples_FlatnessLemmas
public import Theorems.Thm_SNumbers_exists_mem_ker_coords
public import Theorems.Thm_SNumbers_padFin_apply
attribute [local simp] SNumbers.padFin_apply



set_option autoImplicit true
@[expose] public section
public section
universe u
open scoped ENNReal
open SNumbers
variable {𝕜 : Type u} [RCLike 𝕜] {m : ℕ}
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
namespace SNumbers
theorem _root_.solution {V : Submodule 𝕜 (Fin m → 𝕜)} {k : ℕ}
    (w : Fin m → ℝ) (hw : ∀ i, 0 ≤ w i) (hkV : k ≤ Module.finrank 𝕜 V) :
    ∃ x ∈ V, (∀ i, ‖x i‖ ≤ w i) ∧
      k ≤ (Finset.univ.filter (fun i => ‖x i‖ = w i)).card := by
  classical
  set B : Set (Fin m → 𝕜) := {x | x ∈ V ∧ ∀ i, ‖x i‖ ≤ w i} with hBdef
  have hBne : B.Nonempty := ⟨0, V.zero_mem, fun i => by simp only [Pi.zero_apply, norm_zero]; exact hw i⟩
  have hBeq : B = (V : Set (Fin m → 𝕜)) ∩ ⋂ i, {x : Fin m → 𝕜 | ‖x i‖ ≤ w i} := by
    ext x; simp only [hBdef, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter, SetLike.mem_coe]
  have hBclosed : IsClosed B := by
    rw [hBeq]
    refine V.closed_of_finiteDimensional.inter (isClosed_iInter fun i => ?_)
    exact isClosed_le ((continuous_apply i).norm) continuous_const
  have hBbdd : Bornology.IsBounded B := by
    refine (Metric.isBounded_closedBall (x := (0 : Fin m → 𝕜)) (r := ⨆ i, w i)).subset ?_
    intro x hx
    simp only [Metric.mem_closedBall, dist_zero_right]
    refine (pi_norm_le_iff_of_nonneg (Real.iSup_nonneg hw)).mpr fun i => ?_
    exact (hx.2 i).trans (le_ciSup (Finite.bddAbove_range w) i)
  have hBcompact : IsCompact B := Metric.isCompact_of_isClosed_isBounded hBclosed hBbdd
  obtain ⟨x, hxep⟩ := hBcompact.extremePoints_nonempty hBne
  rw [mem_extremePoints_iff_left] at hxep
  obtain ⟨hxB, hxext⟩ := hxep
  set S : Finset (Fin m) := Finset.univ.filter (fun i => ‖x i‖ = w i) with hSdef
  have hxle : ∀ i, ‖x i‖ ≤ w i := hxB.2
  have hmemS : ∀ i, i ∈ S ↔ ‖x i‖ = w i := by
    intro i; rw [hSdef, Finset.mem_filter]; simp [Finset.mem_univ]
  have hcard : Module.finrank 𝕜 V ≤ S.card := by
    by_contra hlt
    push Not at hlt
    obtain ⟨y, hyV, hy0, hyS⟩ := exists_mem_ker_coords (V := V) (A := S) hlt
    have hSc : (Finset.univ.filter (fun i => i ∉ S)).Nonempty := by
      rw [Finset.filter_nonempty_iff]
      by_contra h
      push Not at h
      have : S = Finset.univ := Finset.eq_univ_of_forall fun i => h i (Finset.mem_univ i)
      rw [this, Finset.card_univ, Fintype.card_fin] at hlt
      exact absurd (lt_of_lt_of_le hlt (Submodule.finrank_le V)) (by simp)
    have hMpos : 0 < ‖y‖ := norm_pos_iff.mpr hy0
    set d : ℝ := (Finset.univ.filter (fun i => i ∉ S)).inf' hSc (fun i => w i - ‖x i‖) with hd
    have hdpos : 0 < d := by
      rw [hd, Finset.lt_inf'_iff]
      intro i hi
      rw [Finset.mem_filter] at hi
      have : ‖x i‖ < w i := lt_of_le_of_ne (hxle i) (fun hh => hi.2 ((hmemS i).mpr hh))
      linarith
    set ε : ℝ := d / ‖y‖ with hε
    have hεpos : 0 < ε := div_pos hdpos hMpos
    set c : 𝕜 := RCLike.ofReal ε with hc
    have hcnorm : ‖c‖ = ε := by rw [hc, RCLike.norm_ofReal, abs_of_pos hεpos]
    have hpm : ∀ (μ : 𝕜), ‖μ‖ ≤ ε → ∀ i, ‖x i + μ • y i‖ ≤ w i := by
      intro μ hμ i
      by_cases hi : i ∈ S
      · rw [hyS i hi, smul_zero, add_zero]; exact le_of_eq ((hmemS i).mp hi)
      · have hxiw : ‖x i‖ < w i := lt_of_le_of_ne (hxle i) (fun hh => hi ((hmemS i).mpr hh))
        have hslack : d ≤ w i - ‖x i‖ :=
          hd ▸ Finset.inf'_le _ (by rw [Finset.mem_filter]; exact ⟨Finset.mem_univ i, hi⟩)
        calc ‖x i + μ • y i‖ ≤ ‖x i‖ + ‖μ • y i‖ := norm_add_le _ _
          _ = ‖x i‖ + ‖μ‖ * ‖y i‖ := by rw [norm_smul]
          _ ≤ ‖x i‖ + ε * ‖y‖ := by gcongr; exact norm_le_pi_norm y i
          _ = ‖x i‖ + d := by rw [hε, div_mul_cancel₀ _ (ne_of_gt hMpos)]
          _ ≤ w i := by linarith
    have hmem1 : x + c • y ∈ B :=
      ⟨V.add_mem hxB.1 (V.smul_mem c hyV), fun i => by
        simpa [Pi.add_apply, Pi.smul_apply] using hpm c (le_of_eq hcnorm) i⟩
    have hmem2 : x - c • y ∈ B :=
      ⟨V.sub_mem hxB.1 (V.smul_mem c hyV), fun i => by
        have h := hpm (-c) (by rw [norm_neg]; exact le_of_eq hcnorm) i
        simpa [Pi.sub_apply, Pi.smul_apply, sub_eq_add_neg, neg_smul] using h⟩
    have hseg : x ∈ openSegment ℝ (x + c • y) (x - c • y) :=
      ⟨1/2, 1/2, by norm_num, by norm_num, by norm_num, by module⟩
    have heq := hxext (x + c • y) hmem1 (x - c • y) hmem2 hseg
    have hcy : c • y = 0 := by
      have h2 : x + c • y = x + 0 := by rw [add_zero]; exact heq
      exact add_left_cancel h2
    rcases smul_eq_zero.mp hcy with h | h
    · exact (RCLike.ofReal_ne_zero.mpr (ne_of_gt hεpos)) h
    · exact hy0 h
  exact ⟨x, hxB.1, hxB.2, le_trans hkV hcard⟩
end SNumbers
