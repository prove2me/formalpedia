-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__NZ_exists_gen_1f25671aec83
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:32:29.711161+00:00
-- url     : https://prove2.me/submissions/fb40ea5e-75da-4675-ab87-daa9c180a898

import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NZTypeA
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NZTypeB
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_succ_succ
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_succ_zero
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_zero_succ
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_zero_zero
import Theorems.Thm_P2M_Formalism_GaloisIrreducibility_BorderedIndexCases_zero_ne_succ__49ef2f236cb8
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GaloisIrreducibility.BorderedIndexCases.bord_succ_succ
attribute [local simp] Formalism.GaloisIrreducibility.BorderedIndexCases.bord_succ_zero
attribute [local simp] Formalism.GaloisIrreducibility.BorderedIndexCases.bord_zero_succ
attribute [local simp] Formalism.GaloisIrreducibility.BorderedIndexCases.bord_zero_zero
attribute [local simp] P2M_Formalism_GaloisIrreducibility_BorderedIndexCases_zero_ne_succ__49ef2f236cb8



set_option autoImplicit false
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.BasicNotions.Examples₂.NZ
open Polynomial Formalism.CyclotomicNorms Formalism.CyclotomicNorms.CycleTypeFiniteOrder
variable {g : ℕ} [hg : Fact g.Prime]
namespace Formalism.BasicNotions.Examples₂.NZ
theorem _root_.solution (d : ℕ) (hd : 1 ≤ d) : ∃ u : (Fbar g)ˣ, orderOf u = g ^ d - 1 := by
  classical
  haveI : Fintype (GaloisField g d) := Fintype.ofFinite _
  obtain ⟨x, hx⟩ := IsCyclic.exists_generator (α := (GaloisField g d)ˣ)
  let φ : GaloisField g d →ₐ[ZMod g] Fbar g := IsAlgClosed.lift
  refine ⟨Units.map φ.toRingHom.toMonoidHom x, ?_⟩
  rw [orderOf_injective (Units.map φ.toRingHom.toMonoidHom) (Units.map_injective φ.toRingHom.injective) x,
    orderOf_eq_card_of_forall_mem_zpowers hx, Nat.card_eq_fintype_card, Fintype.card_units]
  congr 1
  first
    | exact GaloisField.card g d (by omega)
    | (rw [← Nat.card_eq_fintype_card]; exact GaloisField.card g d (by omega))
    | simpa [Nat.card_eq_fintype_card] using GaloisField.card g d (by omega)
end Formalism.BasicNotions.Examples₂.NZ
