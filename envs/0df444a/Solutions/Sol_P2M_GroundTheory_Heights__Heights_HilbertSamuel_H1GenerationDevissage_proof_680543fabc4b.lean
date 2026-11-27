-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_H1GenerationDevissage_proof_680543fabc4b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:56:34.711645+00:00
-- url     : https://prove2.me/submissions/d31057f9-29ee-42fe-acf4-5f52cd6669c2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_ImportsSide
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsGradedSubquot
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsGenSESStep
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_KleimanNefness_AlgFiltSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_KleimanNefness_AlgCechSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_H1VanishGeneratedOfLocalizedSubsingleton
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_loc_subsingleton_of_kill_b025ae05f975
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_h1_vanish_generated_of_localized_subsingleton_ba7e604619d4
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_isMGraded_punit_4e0d05a18e96

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
noncomputable section
namespace GroundTheory.Heights₂.Heights.HilbertSamuel
namespace H1GenerationDevissage
theorem _root_.solution (hPF : KH.PrimeFiltStatement) (hSES : KH.CechSESStatement)
    (hGQ : GradedSubquot.Statement) (hGS : GenSESStep.Statement) : H1GenerationDevissage.Statement := by
  intro S _ K _ _ ι _ _ V N hS hP M _ _ _ _ 𝓜 hfin hgr hV e
  obtain ⟨r, m, c, 𝔭, hm, h𝔭, hcol, hspan⟩ := hPF S K ι M 𝓜 hS hfin hgr
  let G : ℕ → Set M := fun j => m '' {l | (l : ℕ) < j}
  let F : ℕ → Submodule (MRingOver S ι) M := fun j => Submodule.span _ (G j)
  have hGh : ∀ j, ∀ x ∈ G j, ∃ c', x ∈ 𝓜 c' := by
    rintro j _ ⟨l, -, rfl⟩
    exact ⟨c l, hm l⟩
  have hFmono : ∀ {i j : ℕ}, i ≤ j → F i ≤ F j := fun hij =>
    Submodule.span_mono (Set.image_mono fun l (hl : (l : ℕ) < _) => lt_of_lt_of_le hl hij)
  have hgrF : ∀ j, KH.IsMGraded S ι (subGrading 𝓜 (F j)) := fun j =>
    (hGQ S K ι M 𝓜 (G j) (G j) hgr (hGh j) (hGh j) le_rfl).1
  have key : ∀ j ≤ r, ∃ c₁ : ℕ, ∀ n : ℕ, c₁ ≤ n →
      Subsingleton (KH.cechHc ι (subGrading 𝓜 (F j)) (e + n • N) 1) ∧
        GeneratedMod S ι (subGrading 𝓜 (F j)) (e + n • N) := by
    intro j
    induction j with
    | zero =>
      intro _
      have hF0 : F 0 = ⊥ := by simp [F, G]
      refine ⟨0, fun n _ => h1_vanish_generated_of_localized_subsingleton
        (fun _ _ => loc_subsingleton_of_kill (Submonoid.one_mem _) fun y => ?_) _ _⟩
      rw [one_smul]
      have hy : (y : M) ∈ (⊥ : Submodule (MRingOver S ι) M) := by
        rw [← hF0]
        exact y.2
      exact Submodule.coe_eq_zero.mp ((Submodule.mem_bot _).1 hy)
    | succ j ih =>
      intro hj
      obtain ⟨c₀, hc₀⟩ := ih (Nat.le_of_succ_le hj)
      let l : Fin r := ⟨j, hj⟩
      let L : Submodule (MRingOver S ι) (F (j + 1)) := (F j).comap (F (j + 1)).subtype
      have hq := (hGQ S K ι M 𝓜 (G j) (G (j + 1)) hgr (hGh j) (hGh (j + 1)) (hFmono (Nat.le_succ j))).2
      have hcolj : ∀ p : MRingOver S ι, p • m l ∈ F j ↔ p ∈ 𝔭 l := fun p => hcol l p
      have hkill : ∀ p ∈ 𝔭 l, ∀ y ∈ F (j + 1), p • y ∈ F j := by
        intro p hp y hy
        induction hy using Submodule.span_induction with
        | mem x hx =>
          obtain ⟨l', hl', rfl⟩ := hx
          rcases Nat.lt_succ_iff_lt_or_eq.1 hl' with h | h
          · exact (F j).smul_mem p (Submodule.subset_span ⟨l', h, rfl⟩)
          · rw [show l' = l from Fin.ext h]
            exact (hcolj p).2 hp
        | zero => rw [smul_zero]; exact (F j).zero_mem
        | add x y _ _ hx hy => rw [smul_add]; exact (F j).add_mem hx hy
        | smul a x _ hx => rw [smul_comm]; exact (F j).smul_mem a hx
      have hann : 𝔭 l ≤ Module.annihilator (MRingOver S ι) (F (j + 1) ⧸ L) := by
        intro p hp
        rw [Module.mem_annihilator]
        intro q
        obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective L q
        rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
        show ((p • y : F (j + 1)) : M) ∈ F j
        rw [Submodule.coe_smul]
        exact hkill p hp y y.2
      have hfinQ : Module.Finite (MRingOver S ι) (F (j + 1) ⧸ L) := by
        have : Module.Finite (MRingOver S ι) (F (j + 1)) :=
          Module.Finite.iff_fg.2 (Submodule.fg_span ((Set.toFinite _).image m))
        infer_instance
      obtain ⟨c₂, hc₂⟩ : ∃ c₂ : ℕ, ∀ n : ℕ, c₂ ≤ n →
          Subsingleton (KH.cechHc ι (quotGrading (subGrading 𝓜 (F (j + 1))) L) (e + n • N) 1) ∧
            GeneratedMod S ι (quotGrading (subGrading 𝓜 (F (j + 1))) L) (e + n • N) := by
        by_cases hrel : IsMultiProjPrime (𝔭 l)
        · exact hP (𝔭 l) hrel (hV.trans (h𝔭 l).2.2) (F (j + 1) ⧸ L) _ hfinQ hq hann e
        · have hirr : ¬ IsRelevant (𝔭 l) := fun h => hrel ⟨(h𝔭 l).1, (h𝔭 l).2.1, h⟩
          simp only [IsRelevant, not_forall, not_exists, not_not] at hirr
          obtain ⟨k, hk⟩ := hirr
          refine ⟨0, fun n _ => h1_vanish_generated_of_localized_subsingleton (fun _ I => ?_) _ _⟩
          obtain ⟨i, hi⟩ := I.2.1 k
          exact loc_subsingleton_of_kill (Submonoid.subset_closure ⟨k, i, hi, rfl⟩)
            (Module.mem_annihilator.1 (hann (hk i)))
      refine ⟨max c₀ c₂, fun n hn => ?_⟩
      have h0 := hc₀ n (le_of_max_le_left hn)
      have h2 := hc₂ n (le_of_max_le_right hn)
      let g := Submodule.inclusion (hFmono (Nat.le_succ j))
      have hex : LinearMap.range g = LinearMap.ker L.mkQ := by
        rw [Submodule.range_inclusion, Submodule.ker_mkQ]
      have hgG : KH.IsMGradedMap S ι (subGrading 𝓜 (F j)) (subGrading 𝓜 (F (j + 1))) g := fun _ _ hx => hx
      have hhG : KH.IsMGradedMap S ι (subGrading 𝓜 (F (j + 1))) (quotGrading (subGrading 𝓜 (F (j + 1))) L)
          L.mkQ := fun _ _ hx => Submodule.mem_map_of_mem hx
      have H := hSES S K ι _ _ _ _ _ _ g L.mkQ (hgrF j) (hgrF (j + 1)) hq hgG hhG
        (Submodule.inclusion_injective _) (Submodule.mkQ_surjective _) hex (e + n • N) 1
      exact ⟨H.1 h0.1 h2.1, hGS S K ι _ _ _ _ _ _ g L.mkQ (hgrF j) (hgrF (j + 1)) hq hgG hhG
        (Submodule.inclusion_injective _) (Submodule.mkQ_surjective _) hex _ h0.1 h0.2 h2.2⟩
  have hFr : F r = ⊤ := by
    rw [← hspan]
    simp [F, G]
  obtain ⟨c₁, hc₁⟩ := key r le_rfl
  refine ⟨c₁, fun n hn => ?_⟩
  obtain ⟨h1, hgen⟩ := hc₁ n hn
  let g := (F r).subtype
  have hex : LinearMap.range g = LinearMap.ker (0 : M →ₗ[MRingOver S ι] PUnit) := by
    rw [Submodule.range_subtype, hFr, LinearMap.ker_zero]
  have hgG : KH.IsMGradedMap S ι (subGrading 𝓜 (F r)) 𝓜 g := fun _ _ hx => hx
  have hhG : KH.IsMGradedMap S ι 𝓜 (fun _ : K → ℤ => (⊥ : Submodule S PUnit)) 0 :=
    fun _ _ _ => Submodule.zero_mem _
  have hU := h1_vanish_generated_of_localized_subsingleton (M := PUnit) (S := S) (ι := ι)
    (fun _ _ => loc_subsingleton_of_kill (Submonoid.one_mem _) fun _ => Subsingleton.elim _ _)
    (fun _ => ⊥) (e + n • N)
  have H := hSES S K ι _ M PUnit _ 𝓜 _ g 0 (hgrF r) hgr isMGraded_punit hgG hhG
    (Submodule.injective_subtype _) (fun _ => ⟨0, Subsingleton.elim _ _⟩) hex (e + n • N) 1
  exact ⟨H.1 h1 hU.1, hGS S K ι _ M PUnit _ 𝓜 _ g 0 (hgrF r) hgr isMGraded_punit hgG hhG
    (Submodule.injective_subtype _) (fun _ => ⟨0, Subsingleton.elim _ _⟩) hex _ h1 hgen hU.2⟩
end H1GenerationDevissage
end GroundTheory.Heights₂.Heights.HilbertSamuel
