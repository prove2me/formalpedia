-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L3.WA.gmap_loc_eq_of_frame
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:47:14.073814+00:00
-- url     : https://prove2.me/submissions/38759273-7b11-4f2f-bebf-5a853c963fe3

import Definitions.Def_Formalism_PeriodIntegrals_HermitianGenusExtension_SemilocalHermitianLattices_ExistsIsomFrame
import Definitions.Def_Formalism_PeriodIntegrals_HermitianGenusExtension_SemilocalHermitianLattices_IsHermSemilocalLocRing
import Definitions.Def_Formalism_PeriodIntegrals_HermitianGenusExtension_SemilocalHermitianLattices_UnimodularOfMemGenusOrtho
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_TraceReal
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IsomAct
import Definitions.Def_Formalism_PeriodIntegrals_HermitianGenusExtension_SemilocalHermitianLattices_GmapLocEqOfFrame
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L3_WA_smul_mem_loc
import Theorems.Thm_Formalism_H_dualEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply


section
open NumberField Module
noncomputable section
namespace ReciprocityTheory.ChartRestriction.L3.WA
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
private theorem mem_locR_of_unimod_lemma {h : V →ₗ⋆[K] V →ₗ[K] K} {L : Submodule (𝓞 K) V}
    {p : Ideal (𝓞 K)} (hu : Formalism.HermitianLatticesTheory.IsUnimodularAt h p L) {x y : V}
    (hx : x ∈ Formalism.HermitianLatticesTheory.loc (K := K) p L) (hy : y ∈ Formalism.HermitianLatticesTheory.loc (K := K) p L) :
    h x y ∈ Formalism.HermitianLatticesTheory.locR (K := K) p := by
  have hu' : Formalism.HermitianLatticesTheory.dualAt h p (Formalism.HermitianLatticesTheory.loc (K := K) p L) = Formalism.HermitianLatticesTheory.loc (K := K) p L := hu
  have hy2 : y ∈ Formalism.HermitianLatticesTheory.dualAt h p (Formalism.HermitianLatticesTheory.loc (K := K) p L) := by
    rw [hu']
    exact hy
  simp only [Formalism.HermitianLatticesTheory.dualAt, Submodule.mem_iInf, Submodule.mem_comap,
    LinearMap.restrictScalars_apply] at hy2
  exact hy2 x hx
private theorem mem_loc_of_mem_lemma_3 {L : Submodule (𝓞 K) V} (p : Ideal (𝓞 K)) {x : V}
    (hx : x ∈ L) : x ∈ Formalism.HermitianLatticesTheory.loc (K := K) p L := by
  show ∃ u ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) p, u • x ∈ L
  exact ⟨1, (Formalism.HermitianLatticesTheory.hcompl (K := K) p).one_mem, by rw [one_smul]; exact hx⟩
private theorem mem_loc_of_smul_lemma_2 {L : Submodule (𝓞 K) V} {p : Ideal (𝓞 K)} {s : 𝓞 K}
    (hs : s ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) p) {y : V}
    (hy : s • y ∈ Formalism.HermitianLatticesTheory.loc (K := K) p L) : y ∈ Formalism.HermitianLatticesTheory.loc (K := K) p L := by
  obtain ⟨t, ht, hty⟩ := hy
  show ∃ u ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) p, u • y ∈ L
  exact ⟨t * s, (Formalism.HermitianLatticesTheory.hcompl (K := K) p).mul_mem ht hs, by rw [mul_smul]; exact hty⟩
end ReciprocityTheory.ChartRestriction.L3.WA
end
end

set_option autoImplicit false
open NumberField Module
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L3 ReciprocityTheory.ChartRestriction.L3.WA
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
namespace ReciprocityTheory.ChartRestriction.L3.WA
theorem _root_.solution {h : V →ₗ⋆[K] V →ₗ[K] K} {L : Submodule (𝓞 K) V}
    {p : Ideal (𝓞 K)} (hp : p.IsPrime) (hu : Formalism.HermitianLatticesTheory.IsUnimodularAt h p L) {n : ℕ} {e : Fin n → V}
    (hspan : Submodule.span K (Set.range e) = ⊤)
    (he : ∀ i j, h (e i) (e j) = if i = j then 1 else 0) {g : V ≃ₗ[K] V}
    (hg : g ∈ Formalism.HermitianLatticesTheory.isom h) (hge : ∀ i, g (e i) ∈ Formalism.HermitianLatticesTheory.loc (K := K) p L) :
    Formalism.HermitianLatticesTheory.gmap g (Formalism.HermitianLatticesTheory.loc (K := K) p (Submodule.span (𝓞 K) (Set.range e))) =
      Formalism.HermitianLatticesTheory.loc (K := K) p L := by
  have hg' : ∀ x y, h (g x) (g y) = h x y := hg
  apply le_antisymm
  · intro y hy
    simp only [Formalism.HermitianLatticesTheory.gmap, Submodule.mem_map] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    obtain ⟨s, hs, hsx⟩ := hx
    refine mem_loc_of_smul_lemma_2 hs ?_
    have hN : Submodule.span (𝓞 K) (Set.range e) ≤
        (Formalism.HermitianLatticesTheory.loc (K := K) p L).comap ((g : V →ₗ[K] V).restrictScalars (𝓞 K)) := by
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact hge i
    have h1 := hN hsx
    rw [Submodule.mem_comap, map_smul ((g : V →ₗ[K] V).restrictScalars (𝓞 K)) s x] at h1
    exact h1
  · intro y hy
    have hz : g.symm y ∈ Submodule.span K (Set.range e) := by
      rw [hspan]
      exact Submodule.mem_top
    rw [Submodule.mem_span_range_iff_exists_fun] at hz
    obtain ⟨c, hc⟩ := hz
    have hcj : ∀ j, c j ∈ Formalism.HermitianLatticesTheory.locR (K := K) p := by
      intro j
      have e2 : h (g (e j)) y = h (e j) (g.symm y) := by
        conv_lhs => rw [← g.apply_symm_apply y]
        exact hg' _ _
      have e1 : c j = h (g (e j)) y := by
        rw [e2, ← hc]
        simp [map_sum, he]
      rw [e1]
      exact mem_locR_of_unimod_lemma hu (hge j) hy
    have hzN : g.symm y ∈ Formalism.HermitianLatticesTheory.loc (K := K) p (Submodule.span (𝓞 K) (Set.range e)) := by
      rw [← hc]
      refine sum_mem (fun i _ => ?_)
      exact smul_mem_loc hp (hcj i) (mem_loc_of_mem_lemma_3 p (Submodule.subset_span ⟨i, rfl⟩))
    simp only [Formalism.HermitianLatticesTheory.gmap, Submodule.mem_map]
    exact ⟨g.symm y, hzN, by simp⟩
end ReciprocityTheory.ChartRestriction.L3.WA
