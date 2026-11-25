-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__Tame_exists_tameGen_8cf65168770b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:47:27.352748+00:00
-- url     : https://prove2.me/submissions/41de069f-5952-49f6-a605-eba152940330

import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataN
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_ExistsTameGen
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__Tame_Near_congr_94ffc6fcca87
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__Tame_exists_gen_d76d46e0bcba
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__Tame_near_left_7dbeede3f3c6
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__Tame_near_right_c2485275af32
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__Tame_closed_of_sat_fdb838e20b19
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__Tame_exists_test_5e3aaaee6b64
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_GaloisCohomology_scalRep_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_ReciprocityTheory_Gal_isClosed_Ine
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply
attribute [local simp] Formalism.GaloisCohomology.scalRep_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.BasicNotions.Examples₂.Tame
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] (A : ValuationSubring Ω)
variable [IsAlgClosure E Ω]
attribute [instance] Test.grp Test.fin
namespace Formalism.BasicNotions.Examples₂.Tame
theorem _root_.solution (p : ℕ) (hp0 : p ≠ 0) (hp : A.valuation (p : Ω) < 1) :
    ∃ γ : G E Ω, TameGenAt A γ := by
  have : IsGalois E Ω := IsAlgClosure.isGalois E Ω
  have : Nonempty (Test E Ω) := ⟨(exists_test (E := E) (0 : Ω)).choose⟩
  let S : Test E Ω → Set (G E Ω) := fun t => (Ine (F := E) A : Set (G E Ω)) ∩
    {γ | ∀ σ ∈ Ine (F := E) A, ∃ n : ℤ, Near A t.φ ((γ ^ n)⁻¹ * σ)}
  have hcl : ∀ t, IsClosed (S t) := fun t => (isClosed_Ine (F := E) A).inter
    (closed_of_sat t _ fun γ γ' e h σ hσ => (h σ hσ).imp fun n hn =>
      hn.congr A (by simp only [map_mul, map_inv, map_zpow, e]))
  obtain ⟨γ, hγ⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed S
    (fun s t => ⟨s.prod t,
      fun γ h => ⟨h.1, fun σ hσ => (h.2 σ hσ).imp fun _ hn => near_left A hn⟩,
      fun γ h => ⟨h.1, fun σ hσ => (h.2 σ hσ).imp fun _ hn => near_right A hn⟩⟩)
    (fun t => exists_gen A p hp0 hp t.A' t.φ t.ho) (fun t => (hcl t).isCompact) hcl
  rw [Set.mem_iInter] at hγ
  refine ⟨γ, (hγ (Classical.arbitrary _)).1, fun σ hσ => ?_⟩
  set C := Subgroup.closure (insert γ {σ : G E Ω | ∀ y : Ω, y ≠ 0 → A.valuation (σ y / y - 1) < 1})
  let U : Test E Ω → Set (G E Ω) := fun t => (C.topologicalClosure : Set (G E Ω)) ∩
    {τ | Near A t.φ (τ⁻¹ * σ)}
  have hU : ∀ t, IsClosed (U t) := fun t => C.isClosed_topologicalClosure.inter
    (closed_of_sat t _ fun τ τ' e h => Near.congr A (by simp only [map_mul, map_inv, e]) h)
  obtain ⟨τ, hτ⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed U
    (fun s t => ⟨s.prod t, fun τ h => ⟨h.1, near_left A h.2⟩, fun τ h => ⟨h.1, near_right A h.2⟩⟩)
    (fun t => by
      obtain ⟨n, hn⟩ := (hγ t).2 σ hσ
      exact ⟨γ ^ n, C.le_topologicalClosure
        (zpow_mem (Subgroup.subset_closure (Set.mem_insert _ _)) n), hn⟩)
    (fun t => (hU t).isCompact) hU
  rw [Set.mem_iInter] at hτ
  have hw : τ⁻¹ * σ ∈ C := Subgroup.subset_closure (Set.mem_insert_of_mem _ fun y hy => by
    obtain ⟨t, ht⟩ := exists_test (E := E) y
    exact (hτ t).2 y hy ht)
  have := mul_mem (hτ (Classical.arbitrary _)).1 (C.le_topologicalClosure hw)
  rwa [mul_inv_cancel_left] at this
end Formalism.BasicNotions.Examples₂.Tame
