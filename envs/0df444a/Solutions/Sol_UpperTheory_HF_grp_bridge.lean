-- Prove2me | solution 1 for UpperTheory.HF.grp_bridge
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:18:57.062909+00:00
-- url     : https://prove2.me/submissions/a36dd988-6b4b-4c35-8cb8-f80ff7aee551

import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_DiffDefs
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_ArtLSpec
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_GrpBridge
import Theorems.Thm_UpperTheory_HF_Formalism_HC_HostRaw_el_pos
import Theorems.Thm_UpperTheory_HF_Formalism_HC_HostRaw_mem_inertG
import Theorems.Thm_UpperTheory_HF_artL_spec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open UpperTheory.HF
open NumberField Ideal Formalism.HC Formalism.FrobeniusOrbits
open scoped Pointwise
private theorem card_eq_of_iff {G G' : Type*} [Group G] [Group G'] (e : G ≃* G') {A : Subgroup G} {B : Subgroup G'}
    (h : ∀ g, g ∈ A ↔ e g ∈ B) : Nat.card A = Nat.card B :=
  Nat.card_congr (e.toEquiv.subtypeEquiv h)
end

set_option autoImplicit false
open UpperTheory.HF
open NumberField Ideal Formalism.HC Formalism.FrobeniusOrbits
open scoped Pointwise
namespace UpperTheory.HF
theorem _root_.solution :
    ∀ {φ : Frame} (H : HostAx φ) {l : ℕ}, l.Prime → ∀ (P : Ideal (𝓞 H.E)) [P.IsPrime] [P.LiesOver (span {(l : ℤ)})], (∀ σ : H.E ≃ₐ[ℚ] H.E, (∀ x : 𝓞 H.E, σ • x - x ∈ P) ↔ H.gal σ ∈ H.inertG l) ∧ (∀ σ : H.E ≃ₐ[ℚ] H.E, σ ∈ MulAction.stabilizer _ P ↔ H.gal σ ∈ H.decG l) ∧ P.ramificationIdx ℤ = H.el l ∧ P.inertiaDeg ℤ = H.nw l ∧ Nat.card (H.decG l) = H.el l * H.nw l ∧ (primesOver (span {(l : ℤ)}) (𝓞 H.E)).ncard * (H.el l * H.nw l) = 4 * φ.ord := by
  intro φ H l hl P _ _
  haveI : Fact l.Prime := ⟨hl⟩
  haveI := H.galois
  haveI hmax : (span {(l : ℤ)}).IsMaximal := Int.ideal_span_isMaximal_of_prime l
  have hI : ∀ σ : H.E ≃ₐ[ℚ] H.E, (∀ x : 𝓞 H.E, σ • x - x ∈ P) ↔ H.gal σ ∈ H.inertG l := fun σ =>
    (H.der.inertia l P σ).trans (H.mem_inertG l _).symm
  have hD : ∀ σ : H.E ≃ₐ[ℚ] H.E, σ ∈ MulAction.stabilizer _ P ↔ H.gal σ ∈ H.decG l := fun σ =>
    (H.der.decomp l P σ).trans ((UpperTheory.HF.artL_spec H.toHostRaw hl).2.2 _).symm
  have hcI : Nat.card (P.inertia Gal(H.E/ℚ)) = H.el l :=
    card_eq_of_iff H.gal (fun σ => AddSubgroup.mem_inertia.trans (hI σ))
  have hcD : Nat.card (MulAction.stabilizer Gal(H.E/ℚ) P) = Nat.card (H.decG l) :=
    card_eq_of_iff H.gal hD
  have hle : H.inertG l ≤ H.decG l := le_sup_left
  have hmul : Nat.card (H.decG l) = H.el l * H.nw l := by
    rw [← ((H.inertG l).subgroupOf (H.decG l)).card_mul_index,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv]
    rfl
  have he : (span {(l : ℤ)}).ramificationIdxIn (𝓞 H.E) = H.el l := by
    rw [← hcI, card_inertia_eq_ramificationIdxIn (G := Gal(H.E/ℚ)) (span {(l : ℤ)}) P]
  have hf : (span {(l : ℤ)}).inertiaDegIn (𝓞 H.E) = H.nw l := by
    have h := card_stabilizer_eq (G := Gal(H.E/ℚ)) (span {(l : ℤ)}) P
    rw [hcD, hmul, he] at h
    exact (Nat.eq_of_mul_eq_mul_left (H.el_pos l) h).symm
  refine ⟨hI, hD, ?_, ?_, hmul, ?_⟩
  · rw [← he, ramificationIdxIn_eq_ramificationIdx (span {(l : ℤ)}) P Gal(H.E/ℚ)]
  · rw [← hf, inertiaDegIn_eq_inertiaDeg (span {(l : ℤ)}) P Gal(H.E/ℚ)]
  · rw [← he, ← hf, ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn (span {(l : ℤ)}) (𝓞 H.E) Gal(H.E/ℚ),
      IsGalois.card_aut_eq_finrank, H.der.finrank_E]
end UpperTheory.HF
