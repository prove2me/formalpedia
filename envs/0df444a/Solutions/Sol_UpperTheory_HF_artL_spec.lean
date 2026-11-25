-- Prove2me | solution 1 for UpperTheory.HF.artL_spec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:49:52.335022+00:00
-- url     : https://prove2.me/submissions/34ddc416-357e-4fac-9ed4-1111f58df59f

import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_DiffDefs
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_ArtLSpec
import Theorems.Thm_Formalism_FrobeniusOrbits_Group_key
import Theorems.Thm_Formalism_FrobeniusOrbits_ThickOrbit_key
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_UpperTheory_HF_Formalism_HC_HostRaw_mem_inertG
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv


section
open UpperTheory.HF
open NumberField Ideal Formalism.HC Formalism.FrobeniusOrbits
open scoped Pointwise
private theorem exists_unit {N l : ℕ} (hN : N ≠ 0) (hl : l.Prime) :
    ∃ u : (ZMod N)ˣ, (u : ZMod N).val ≡ l [MOD ordCompl[l] N] ∧ (u : ZMod N).val ≡ 1 [MOD ordProj[l] N] := by
  have hcl : Nat.Coprime l (ordCompl[l] N) := Nat.coprime_ordCompl hl hN
  have hcop : Nat.Coprime (ordCompl[l] N) (ordProj[l] N) := (Nat.Coprime.pow_left _ hcl).symm
  obtain ⟨k, hk1, hk2⟩ := Nat.chineseRemainder hcop l 1
  have hc1 : Nat.Coprime k (ordCompl[l] N) := by
    unfold Nat.Coprime
    rw [Nat.ModEq.gcd_eq hk1]
    exact hcl
  have hc2 : Nat.Coprime k (ordProj[l] N) := by
    unfold Nat.Coprime
    rw [Nat.ModEq.gcd_eq hk2]
    simp
  have hco : Nat.Coprime k N := by
    have h := Nat.Coprime.mul_right hc2 hc1
    rwa [Nat.ordProj_mul_ordCompl_eq_self] at h
  refine ⟨ZMod.unitOfCoprime k hco, ?_, ?_⟩
  · rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast]
    exact ((Nat.mod_modEq k N).of_dvd (Nat.ordCompl_dvd N l)).trans hk1
  · rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast]
    exact ((Nat.mod_modEq k N).of_dvd (Nat.ordProj_dvd N l)).trans hk2
private theorem unit_unique {N l : ℕ} (hN : N ≠ 0) (hl : l.Prime) {u v : (ZMod N)ˣ}
    (h1 : (u : ZMod N).val ≡ (v : ZMod N).val [MOD ordCompl[l] N])
    (h2 : (u : ZMod N).val ≡ (v : ZMod N).val [MOD ordProj[l] N]) : u = v := by
  have hcop : Nat.Coprime (ordProj[l] N) (ordCompl[l] N) :=
    Nat.Coprime.pow_left _ (Nat.coprime_ordCompl hl hN)
  have h := (Nat.modEq_and_modEq_iff_modEq_mul hcop).mp ⟨h2, h1⟩
  rw [Nat.ordProj_mul_ordCompl_eq_self] at h
  haveI : NeZero N := ⟨hN⟩
  apply Units.ext
  apply ZMod.val_injective
  have hu := ZMod.val_lt (u : ZMod N)
  have hv := ZMod.val_lt (v : ZMod N)
  unfold Nat.ModEq at h
  rwa [Nat.mod_eq_of_lt hu, Nat.mod_eq_of_lt hv] at h
private theorem val_iff {N f : ℕ} [NeZero N] (hf : f ∣ N) (u : (ZMod N)ˣ) (a : ℕ) :
    (u : ZMod N).val ≡ a [MOD f] ↔ ((ZMod.unitsMap hf u : (ZMod f)ˣ) : ZMod f) = (a : ZMod f) := by
  rw [ZMod.unitsMap_val, ZMod.cast_eq_val, ZMod.natCast_eq_natCast_iff]
end

set_option autoImplicit false
open UpperTheory.HF
open NumberField Ideal Formalism.HC Formalism.FrobeniusOrbits
open scoped Pointwise
namespace UpperTheory.HF
theorem _root_.solution :
    ∀ {φ : Frame} (H : HostRaw φ) {l : ℕ}, l.Prime → (∃ u : (ZMod H.condN)ˣ, (u : ZMod H.condN).val ≡ l [MOD ordCompl[l] H.condN] ∧ (u : ZMod H.condN).val ≡ 1 [MOD ordProj[l] H.condN] ∧ H.artL l = H.art u) ∧ (∀ u : (ZMod H.condN)ˣ, (u : ZMod H.condN).val ≡ l [MOD ordCompl[l] H.condN] → (u : ZMod H.condN).val ≡ 1 [MOD ordProj[l] H.condN] → H.art u = H.artL l) ∧ ∀ g : φ.GG, g ∈ H.decG l ↔ ∃ (u : (ZMod H.condN)ˣ) (k : ℕ), (u : ZMod H.condN).val ≡ l ^ k [MOD ordCompl[l] H.condN] ∧ g = H.art u := by
  intro φ H l hl
  haveI : NeZero H.condN := ⟨H.condN_ne_zero⟩
  have hN : H.condN ≠ 0 := H.condN_ne_zero
  have hex := exists_unit hN hl
  have hart : H.artL l = H.art hex.choose := by
    unfold UpperTheory.HF.Formalism.HC.HostRaw.artL
    rw [dif_pos hex]
  obtain ⟨hc1, hc2⟩ := hex.choose_spec
  have part2 : ∀ u : (ZMod H.condN)ˣ, (u : ZMod H.condN).val ≡ l [MOD ordCompl[l] H.condN] →
      (u : ZMod H.condN).val ≡ 1 [MOD ordProj[l] H.condN] → H.art u = H.artL l := by
    intro u hu1 hu2
    rw [hart, unit_unique hN hl (hu1.trans hc1.symm) (hu2.trans hc2.symm)]
  refine ⟨⟨hex.choose, hc1, hc2, hart⟩, part2, ?_⟩
  have hA : ordCompl[l] H.condN ∣ H.condN := Nat.ordCompl_dvd _ _
  haveI : NeZero (ordCompl[l] H.condN) :=
    ⟨fun h => hN (Nat.eq_zero_of_zero_dvd (h ▸ hA))⟩
  obtain ⟨lA, hlA⟩ : ∃ w : (ZMod (ordCompl[l] H.condN))ˣ, (w : ZMod (ordCompl[l] H.condN)) = (l : ZMod _) :=
    ⟨ZMod.unitOfCoprime l (Nat.coprime_ordCompl hl hN), ZMod.coe_unitOfCoprime _ _⟩
  have key : ∀ (u : (ZMod H.condN)ˣ) (k : ℕ),
      (u : ZMod H.condN).val ≡ l ^ k [MOD ordCompl[l] H.condN] ↔ ZMod.unitsMap hA u = lA ^ k := by
    intro u k
    rw [val_iff hA u (l ^ k), Units.ext_iff, Units.val_pow_eq_pow_val, hlA, Nat.cast_pow]
  let T : Subgroup φ.GG := ((Subgroup.zpowers lA).comap (ZMod.unitsMap hA)).map H.art
  have memT : ∀ g, g ∈ T ↔ ∃ (u : (ZMod H.condN)ˣ) (k : ℕ),
      (u : ZMod H.condN).val ≡ l ^ k [MOD ordCompl[l] H.condN] ∧ g = H.art u := by
    intro g
    simp only [T, Subgroup.mem_map, Subgroup.mem_comap, ← mem_powers_iff_mem_zpowers,
      Submonoid.mem_powers_iff]
    constructor
    · rintro ⟨u, ⟨k, hk⟩, rfl⟩
      exact ⟨u, k, (key u k).mpr hk.symm, rfl⟩
    · rintro ⟨u, k, hk, rfl⟩
      exact ⟨u, ⟨k, ((key u k).mp hk).symm⟩, rfl⟩
  have hle1 : UpperTheory.HF.Formalism.HC.HostRaw.decG H l ≤ T := by
    unfold UpperTheory.HF.Formalism.HC.HostRaw.decG
    refine sup_le ?_ ?_
    · intro g hg
      obtain ⟨u, hu, rfl⟩ := (UpperTheory.HF.Formalism.HC.HostRaw.mem_inertG H l g).mp hg
      exact (memT _).mpr ⟨u, 0, by simpa using hu, rfl⟩
    · rw [Subgroup.zpowers_le, hart]
      exact (memT _).mpr ⟨hex.choose, 1, by simpa using hc1, rfl⟩
  have hu1 : ZMod.unitsMap hA hex.choose = lA := by
    have h := (key hex.choose 1).mp (by simpa using hc1)
    simpa using h
  have hle2 : T ≤ UpperTheory.HF.Formalism.HC.HostRaw.decG H l := by
    intro g hg
    obtain ⟨u, k, hk, rfl⟩ := (memT g).mp hg
    have hw : ((u * (hex.choose ^ k)⁻¹ : (ZMod H.condN)ˣ) : ZMod H.condN).val ≡ 1
        [MOD ordCompl[l] H.condN] := by
      have h := (key (u * (hex.choose ^ k)⁻¹) 0).mpr
        (by rw [map_mul, map_inv, map_pow, hu1, (key u k).mp hk]; simp)
      simpa using h
    have hmem : H.art (u * (hex.choose ^ k)⁻¹) ∈ UpperTheory.HF.Formalism.HC.HostRaw.inertG H l :=
      (UpperTheory.HF.Formalism.HC.HostRaw.mem_inertG H l _).mpr ⟨_, hw, rfl⟩
    have heq : H.art u = H.art (u * (hex.choose ^ k)⁻¹) * H.artL l ^ k := by
      rw [hart, map_mul, map_inv, map_pow, inv_mul_cancel_right]
    rw [heq]
    unfold UpperTheory.HF.Formalism.HC.HostRaw.decG
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hmem)
      (Subgroup.pow_mem _ (Subgroup.mem_sup_right (Subgroup.mem_zpowers _)) _)
  intro g
  rw [show UpperTheory.HF.Formalism.HC.HostRaw.decG H l = T from le_antisymm hle1 hle2]
  exact memT g
end UpperTheory.HF
