-- Prove2me | solution 1 for PI.VolStabSW.um_sigmaCompact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:44:47.685268+00:00
-- url     : https://prove2.me/submissions/d0ad3572-6ff0-49e4-9c76-571990d84a4e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_FibInfEx
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicLocalCompactness_T2SpaceTensorProductFiniteExtension
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_Unimod
import Theorems.Thm_PI_VolStabSW_um_self_mem_D
import Theorems.Thm_PI_VolStabSW_um_D_eq
import Theorems.Thm_PI_VolStabSW_um_D_open
import Theorems.Thm_PI_VolStabSW_um_D_smul
import Theorems.Thm_PI_VolStabSW_um_smulInv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabSW
open MeasureTheory Measure Topology Set Function
open scoped Pointwise ENNReal NNReal
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [MeasurableSpace G] [BorelSpace G]
namespace PI.VolStabSW
theorem _root_.solution (Γ : Subgroup G) [Countable Γ] (μ : Measure G) [IsHaarMeasure μ]
    (𝓕 : Set G) (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) (hfin : μ 𝓕 < ⊤) : SigmaCompactSpace G := by
  have := um_smulInv Γ μ
  obtain ⟨V, hVc, hV1⟩ := exists_compact_mem_nhds (1 : G)
  set W : Set G := V ∪ V⁻¹ with hWdef
  have hWc : IsCompact W := hVc.union hVc.inv
  have hWinv : W⁻¹ = W := by rw [hWdef, Set.union_inv, inv_inv, union_comm]
  set H : Subgroup G := Subgroup.closure V with hHdef
  have hHo : IsOpen (H : Set G) :=
    Subgroup.isOpen_of_mem_nhds H (Filter.mem_of_superset hV1 Subgroup.subset_closure)
  have hPc : ∀ n : ℕ, IsCompact (W ^ n) := by
    intro n
    induction n with
    | zero => rw [pow_zero]; exact isCompact_singleton
    | succ n ih => rw [pow_succ]; exact ih.mul hWc
  have hHc : (H : Set G) ⊆ ⋃ n : ℕ, W ^ n := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx => exact mem_iUnion.2 ⟨1, by rw [pow_one]; exact Or.inl hx⟩
    | one => exact mem_iUnion.2 ⟨0, by rw [pow_zero]; exact Set.mem_one.2 rfl⟩
    | mul x y _ _ hx hy =>
      obtain ⟨m, hm⟩ := mem_iUnion.1 hx
      obtain ⟨n, hn⟩ := mem_iUnion.1 hy
      exact mem_iUnion.2 ⟨m + n, by rw [pow_add]; exact Set.mul_mem_mul hm hn⟩
    | inv x _ hx =>
      obtain ⟨n, hn⟩ := mem_iUnion.1 hx
      refine mem_iUnion.2 ⟨n, ?_⟩
      have h' : (W ^ n)⁻¹ = W ^ n := by rw [← inv_pow, hWinv]
      rw [← h']
      exact Set.inv_mem_inv.2 hn
  let ι := ↥(range (umD Γ H))
  have hpos : ∀ d : ι, 0 < μ ((d : Set G) ∩ 𝓕) := by
    rintro ⟨d, x, rfl⟩
    refine pos_iff_ne_zero.2 fun h0 => ?_
    have h1 := h𝓕.measure_zero_of_invariant (umD Γ H x) (um_D_smul Γ H x) h0
    exact (um_D_open Γ H hHo x).measure_ne_zero μ ⟨x, um_self_mem_D Γ H x⟩ h1
  have hdisj : Pairwise (Disjoint on fun d : ι => (d : Set G) ∩ 𝓕) := by
    rintro ⟨d, x, rfl⟩ ⟨d', x', rfl⟩ hne
    refine Disjoint.mono inter_subset_left inter_subset_left ?_
    refine Set.disjoint_left.2 fun z hz hz' => hne ?_
    exact Subtype.ext ((um_D_eq Γ H hz).symm.trans (um_D_eq Γ H hz'))
  have hctbl : Countable ι := by
    have := Measure.countable_meas_pos_of_disjoint_of_meas_iUnion_ne_top₀ μ
      (As := fun d : ι => (d : Set G) ∩ 𝓕)
      (fun d => by
        rcases d with ⟨_, x, rfl⟩
        exact (um_D_open Γ H hHo x).measurableSet.nullMeasurableSet.inter h𝓕.nullMeasurableSet)
      hdisj.aedisjoint
      (ne_top_of_le_ne_top hfin.ne (measure_mono (iUnion_subset fun _ => inter_subset_right)))
    have hall : {d : ι | 0 < μ ((d : Set G) ∩ 𝓕)} = univ := eq_univ_of_forall hpos
    rw [hall] at this
    exact countable_univ_iff.1 this
  let rep : ι → G := fun d => d.2.choose
  have hrep : ∀ d : ι, umD Γ H (rep d) = d := fun d => d.2.choose_spec
  let K : ι × Γ × ℕ → Set G := fun p => (fun z => (p.2.1 : G) * rep p.1 * z) '' (W ^ p.2.2)
  have hK : ∀ p, IsCompact (K p) := fun p => (hPc p.2.2).image (by fun_prop)
  have hcov : (⋃ p, K p) = univ := by
    refine eq_univ_of_forall fun y => ?_
    let d : ι := ⟨umD Γ H y, y, rfl⟩
    have hy : y ∈ umD Γ H (rep d) := by rw [hrep d]; exact um_self_mem_D Γ H y
    obtain ⟨γ, hγ, h, hh, hyeq⟩ := hy
    obtain ⟨n, hn⟩ := mem_iUnion.1 (hHc hh)
    exact mem_iUnion.2 ⟨(d, ⟨γ, hγ⟩, n), h, hn, hyeq.symm⟩
  rw [← isSigmaCompact_univ_iff, ← hcov]
  exact isSigmaCompact_iUnion_of_isCompact K hK
end PI.VolStabSW
