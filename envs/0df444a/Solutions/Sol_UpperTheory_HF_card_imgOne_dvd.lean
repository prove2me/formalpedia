-- Prove2me | solution 1 for UpperTheory.HF.card_imgOne_dvd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T15:59:47.300474+00:00
-- url     : https://prove2.me/submissions/90f16e8e-fc52-4f06-a6ba-c1cd6fa89f51

import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_DiffDefs
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_RdArith
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_CardImgOneDvd
import Theorems.Thm_UpperTheory_HF_Formalism_HC_HostRaw_mem_unitsOne

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
private theorem card_map_dvd {G G' : Type*} [Group G] [Group G'] (a : G →* G') {A B : Subgroup G} (h : A ≤ B) :
    Nat.card (B.map a) ∣ Nat.card (A.map a) * A.relIndex B := by
  have hAB : A.map a ≤ B.map a := Subgroup.map_mono h
  have hc : Nat.card (B.map a) = Nat.card (A.map a) * (A.map a).relIndex (B.map a) := by
    rw [Subgroup.relIndex, ← Subgroup.card_mul_index ((A.map a).subgroupOf (B.map a))]
    congr 1
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAB).toEquiv
  rw [hc]
  apply mul_dvd_mul_left
  rw [← Subgroup.relIndex_comap]
  exact Subgroup.relIndex_dvd_of_le_left B (Subgroup.le_comap_map a A)
private theorem index_unitsOne {φ : Frame} (H : HostRaw φ) {f : ℕ} (hf : f ∣ H.condN) :
    (H.unitsOne f).index = f.totient := by
  have hN : H.condN ≠ 0 := H.condN_ne_zero
  have hf0 : f ≠ 0 := by
    rintro rfl
    exact hN (zero_dvd_iff.1 hf)
  have hg : Nat.gcd f H.condN = f := Nat.gcd_eq_left hf
  haveI : NeZero (Nat.gcd f H.condN) := ⟨by rw [hg]; exact hf0⟩
  unfold HostRaw.unitsOne
  rw [Subgroup.index_ker, MonoidHom.range_eq_top.2 (ZMod.unitsMap_surjective _), Subgroup.card_top,
    Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, hg]
end

set_option autoImplicit false
open UpperTheory.HF
open NumberField Ideal Formalism.HC Formalism.FrobeniusOrbits
open scoped Pointwise
namespace UpperTheory.HF
theorem _root_.solution :
    ∀ {φ : Frame} (H : HostRaw φ) {f g : ℕ}, f ∣ g → g ∣ H.condN → Nat.card (H.imgOne f) ∣ Nat.card (H.imgOne g) * (g.totient / f.totient) := by
  intro φ H f g hfg hg
  have hf : f ∣ H.condN := hfg.trans hg
  have hle : H.unitsOne g ≤ H.unitsOne f := by
    intro u hu
    rw [H.mem_unitsOne hg] at hu
    rw [H.mem_unitsOne hf]
    exact Nat.ModEq.of_dvd hfg hu
  have hd := card_map_dvd H.art hle
  have hidx := Subgroup.relIndex_mul_index hle
  rw [index_unitsOne H hf, index_unitsOne H hg] at hidx
  have hf0 : 0 < f := by
    rcases Nat.eq_zero_or_pos f with h0 | h0
    · exfalso
      subst h0
      exact H.condN_ne_zero (zero_dvd_iff.1 hf)
    · exact h0
  have htot : 0 < f.totient := Nat.totient_pos.2 hf0
  have hr : g.totient / f.totient = (H.unitsOne g).relIndex (H.unitsOne f) := by
    rw [← hidx, Nat.mul_div_cancel _ htot]
  rw [hr]
  exact hd
end UpperTheory.HF
