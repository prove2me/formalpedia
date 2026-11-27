-- Prove2me | solution 1 for UpperTheory.GL.ch_cond
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:48:51.686617+00:00
-- url     : https://prove2.me/submissions/ee07467d-b689-4612-9b41-e417ec250cd1

import Definitions.Def_Development_AutomorphicArithmetic_PrimitiveCosets_CoreAtH
import Definitions.Def_Development_AutomorphicArithmetic_PrimitiveCosets_ToEBij
import Definitions.Def_Development_AutomorphicArithmetic_ConductorsKronecker_ChCond
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_HC_HostRaw_coprime_q_d
import Theorems.Thm_Formalism_HC_HostRaw_d_dvd_condN
import Theorems.Thm_Formalism_HC_HostRaw_d_ne_two
import Theorems.Thm_Formalism_HC_HostRaw_q_dvd_condN
import Theorems.Thm_Formalism_HC_HostRaw_q_ne_d
import Theorems.Thm_Formalism_HC_HostRaw_q_ne_two
import Theorems.Thm_Formalism_HC_jacobi_congr
import Theorems.Thm_Formalism_LFunctionChainParameters_LHost_cosetMean_of_nontrivial
import Theorems.Thm_Formalism_LFunctionChainParameters_LHost_cosetMean_of_trivial
import Theorems.Thm_Formalism_LFunctionChainParameters_LHost_dirChar_unit
import Theorems.Thm_Formalism_LFunctionChainParameters_LHost_exists_unit_crt
import Theorems.Thm_Formalism_LFunctionChainParameters_LHost_frobUnit_modEq
import Theorems.Thm_Formalism_LFunctionChainParameters_LHost_inertia_conductor
import Theorems.Thm_Formalism_LFunctionChainParameters_LHost_jac_self
import Theorems.Thm_Formalism_LFunctionChainParameters_LHost_mem_inertia_iff
import Theorems.Thm_Formalism_LFunctionChainParameters_LHost_mem_localUnits_iff
import Theorems.Thm_Formalism_LFunctionChainParameters_LHost_sgn2_toAdd_eq_ite
import Theorems.Thm_Formalism_LFunctionChainParameters_LHost_unitsMap_eq_one_iff
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
open UpperTheory.Comparison₂ Deduction.CH Formalism Formalism.HC Formalism.D5 Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LHost NumberField Ideal
section
variable {A : Type} [AddCommGroup A] [Fintype A] [DecidableEq A]
private theorem UpperTheory.GL.primVal_of_periodic {N c : ℕ} [NeZero N] (q d : ℕ)
    (r : (ZMod N)ˣ →* Multiplicative (E0 × A)) (ψ : AddChar (E0 × A) ℂ) (F : ℕ →* ℤ) (hc : c ∣ N)
    (hF : ∀ x y, x ≡ y [MOD c] → F x = F y)
    (hψ : ∀ u : (ZMod N)ˣ, ψ (Multiplicative.toAdd (r u)) = ((F (u : ZMod N).val : ℤ) : ℂ))
    (hram : ∀ p, p.Prime → p ∣ c → F p = 0 ∧
      ∃ u : (ZMod N)ˣ, (u : ZMod N).val ≡ 1 [MOD ordCompl[p] N] ∧ F (u : ZMod N).val = -1)
    (n : ℕ) (hn : n ≠ 0) : primVal (cftData q d r) ψ n = ((F n : ℤ) : ℂ) := by
  conv_rhs => rw [← Nat.prod_factorization_pow_eq_self hn]
  rw [Nat.prod_factorization_eq_prod_primeFactors, map_prod, Int.cast_prod]
  unfold primVal
  apply Finset.prod_congr rfl
  intro p hp
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hi : n.factorization p ≠ 0 := by
    have := (Nat.support_factorization n ▸ hp : p ∈ n.factorization.support)
    exact Finsupp.mem_support_iff.1 this
  rw [map_pow, Int.cast_pow]
  by_cases hpc : p ∣ c
  · obtain ⟨h0, u, hu, hu1⟩ := hram p hpp hpc
    rw [cosetMean_of_nontrivial, h0, Int.cast_zero, zero_pow hi]
    intro h
    have := h _ ((mem_inertia_iff q d r p _).2 ⟨u, (mem_localUnits_iff p u).2 hu, rfl⟩)
    rw [hψ, hu1] at this
    norm_num at this
  · have hcd : c ∣ ordCompl[p] N := Nat.dvd_ordCompl_of_dvd_not_dvd hc hpc
    rw [cosetMean_of_trivial, AddChar.map_nsmul_eq_pow]
    · congr 1
      change ψ (Multiplicative.toAdd (r (frobUnit N p))) = _
      rw [hψ, hF _ _ ((frobUnit_modEq hpp).1.of_dvd hcd)]
    · intro x hx
      obtain ⟨u, hu, rfl⟩ := (mem_inertia_iff q d r p _).1 hx
      rw [hψ, hF _ _ (((mem_localUnits_iff p u).1 hu).of_dvd hcd), map_one, Int.cast_one]
private theorem UpperTheory.GL.conductor_of_periodic {N c : ℕ} [NeZero N]
    (r : (ZMod N)ˣ →* Multiplicative (E0 × A)) (ψ : AddChar (E0 × A) ℂ) (F : ℕ →* ℤ) (hc : c ∣ N) (hp : c.Prime)
    (hF : ∀ x y, x ≡ y [MOD c] → F x = F y)
    (hψ : ∀ u : (ZMod N)ˣ, ψ (Multiplicative.toAdd (r u)) = ((F (u : ZMod N).val : ℤ) : ℂ))
    (hram : ∃ u : (ZMod N)ˣ, (u : ZMod N).val ≡ 1 [MOD ordCompl[c] N] ∧ F (u : ZMod N).val = -1) :
    (dirChar r ψ).conductor = c := by
  apply Nat.dvd_antisymm
  · rw [← DirichletCharacter.mem_conductorSet_iff_conductor_dvd _ hc,
      DirichletCharacter.mem_conductorSet_iff,
      DirichletCharacter.factorsThrough_iff_ker_unitsMap hc]
    intro u hu
    rw [MonoidHom.mem_ker, unitsMap_eq_one_iff] at hu
    rw [MonoidHom.mem_ker, Units.ext_iff, MulChar.coe_toUnitHom, dirChar_unit, Units.val_one, hψ, hF _ _ hu,
      map_one, Int.cast_one]
  · by_contra hh
    obtain ⟨u, hu, hu1⟩ := hram
    have := (inertia_conductor (H := A) N 0 0 r ψ c (NeZero.ne N) hp).2 hh _
      ((mem_inertia_iff 0 0 r c _).2 ⟨u, (mem_localUnits_iff c u).2 hu, rfl⟩)
    rw [hψ, hu1] at this
    norm_num at this
end
private theorem UpperTheory.GL.exists_nonres {N l : ℕ} [NeZero N] (hl : l.Prime) (h2 : l ≠ 2) (hN : l ∣ N) :
    ∃ u : (ZMod N)ˣ, (u : ZMod N).val ≡ 1 [MOD ordCompl[l] N] ∧ jacobiSym ((u : ZMod N).val : ℤ) l = -1 := by
  have : Fact l.Prime := ⟨hl⟩
  have hN0 := NeZero.ne N
  have hcop : (ordProj[l] N).Coprime (ordCompl[l] N) := (Nat.coprime_ordCompl hl hN0).pow_left _
  have hlP : l ∣ ordProj[l] N := Nat.dvd_ordProj_of_dvd hN0 hl hN
  have : NeZero (ordProj[l] N) := ⟨pow_ne_zero _ hl.ne_zero⟩
  obtain ⟨x, hx⟩ := quadraticChar_exists_neg_one' (F := ZMod l) (by rwa [ZMod.ringChar_zmod_n])
  obtain ⟨y, hy⟩ := ZMod.unitsMap_surjective hlP x
  obtain ⟨u, hu1, hu2⟩ := exists_unit_crt (Nat.ordProj_mul_ordCompl_eq_self N l).symm hcop
      (Nat.ordProj_dvd N l) (Nat.ordCompl_dvd N l) y 1
  refine ⟨u, (unitsMap_eq_one_iff _ u).1 hu2, ?_⟩
  have h3 : ZMod.unitsMap hN u = x := by
    rw [← hy, ← hu1, ← MonoidHom.comp_apply, ZMod.unitsMap_comp]
  rw [← jacobiSym.legendreSym.to_jacobiSym, legendreSym, Int.cast_natCast, ← hx, ← h3, ZMod.unitsMap_val,
    ZMod.natCast_val]
private theorem UpperTheory.GL.sgn_val (s : ℤˣ) :
    (if Multiplicative.toAdd (Formalism.LFunctionChainParameters.LHost.sgn2 s) = 0 then (1 : ℂ) else -1) = (((s : ℤˣ) : ℤ) : ℂ) := by
  rw [sgn2_toAdd_eq_ite]
  rcases Int.units_eq_one_or s with rfl | rfl <;> simp
end

set_option autoImplicit false
open UpperTheory.Comparison₂ Deduction.CH Formalism Formalism.HC Formalism.D5 Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LHost NumberField Ideal
namespace UpperTheory.GL
theorem _root_.solution :
    ∀ {φ : Frame} (H : HostAx φ), (dirChar (recH H.toHostRaw) chC).conductor = H.d ∧
      (∀ n : ℕ, n ≠ 0 → primVal (arith H.toHostRaw) chC n = ((jacobiSym (n : ℤ) H.d : ℤ) : ℂ)) ∧
      (H.PsQ → (dirChar (recH H.toHostRaw) psC).conductor = H.q ∧
        (∀ n : ℕ, n ≠ 0 → primVal (arith H.toHostRaw) psC n = ((jacobiSym (n : ℤ) H.q : ℤ) : ℂ)) ∧
        ∀ n : ℕ, n ≠ 0 → primVal (arith H.toHostRaw) chpsC n = ((jacobiSym (n : ℤ) H.d * jacobiSym (n : ℤ) H.q : ℤ) : ℂ)) := by
  intro φ H
  have hd := H.d_prime
  have hq := H.q_prime
  have ed := exists_nonres hd H.d_ne_two H.d_dvd_condN
  have eq := exists_nonres hq H.q_ne_two H.q_dvd_condN
  have hch : ∀ u : (ZMod H.condN)ˣ, (chC : AddChar (E0 × φ.A) ℂ) (Multiplicative.toAdd (recH H.toHostRaw u))
      = ((jac H.d (u : ZMod H.condN).val : ℤ) : ℂ) := by
    intro u
    change _ = ((jacobiSym _ _ : ℤ) : ℂ)
    rw [← H.der.art_ch u]
    exact sgn_val _
  have one : ∀ l : ℕ, l.Prime → (∃ u : (ZMod H.condN)ˣ, (u : ZMod H.condN).val ≡ 1 [MOD ordCompl[l] H.condN] ∧
      jacobiSym ((u : ZMod H.condN).val : ℤ) l = -1) → ∀ p, p.Prime → p ∣ l → jac l p = 0 ∧
      ∃ u : (ZMod H.condN)ˣ, (u : ZMod H.condN).val ≡ 1 [MOD ordCompl[p] H.condN] ∧
        jac l (u : ZMod H.condN).val = -1 := by
    intro l hl e p hp hpl
    obtain rfl := (Nat.prime_dvd_prime_iff_eq hp hl).1 hpl
    exact ⟨jac_self p hp.one_lt, e⟩
  refine ⟨conductor_of_periodic _ _ (jac H.d) H.d_dvd_condN hd (fun _ _ h => jacobi_congr h) hch ed,
    primVal_of_periodic _ _ _ _ (jac H.d) H.d_dvd_condN (fun _ _ h => jacobi_congr h) hch (one _ hd ed), fun hP => ?_⟩
  have hps : ∀ u : (ZMod H.condN)ˣ, (psC : AddChar (E0 × φ.A) ℂ) (Multiplicative.toAdd (recH H.toHostRaw u))
      = ((jac H.q (u : ZMod H.condN).val : ℤ) : ℂ) := by
    intro u
    change _ = ((jacobiSym _ _ : ℤ) : ℂ)
    rw [← hP u]
    exact sgn_val _
  refine ⟨conductor_of_periodic _ _ (jac H.q) H.q_dvd_condN hq (fun _ _ h => jacobi_congr h) hps eq,
    primVal_of_periodic _ _ _ _ (jac H.q) H.q_dvd_condN (fun _ _ h => jacobi_congr h) hps (one _ hq eq), ?_⟩
  refine primVal_of_periodic (c := H.d * H.q) _ _ _ _ (jac H.d * jac H.q)
    (H.coprime_q_d.symm.mul_dvd_of_dvd_of_dvd H.d_dvd_condN H.q_dvd_condN) (fun x y h => ?_) (fun u => ?_) ?_
  · change jacobiSym _ _ * jacobiSym _ _ = jacobiSym _ _ * jacobiSym _ _
    rw [jacobi_congr (h.of_dvd (dvd_mul_right _ _)), jacobi_congr (h.of_dvd (dvd_mul_left _ _))]
  · unfold chpsC
    rw [AddChar.mul_apply, hch, hps, MonoidHom.mul_apply, Int.cast_mul]
  · intro p hp hpl
    rcases hp.dvd_mul.1 hpl with h | h
    · obtain rfl := (Nat.prime_dvd_prime_iff_eq hp hd).1 h
      obtain ⟨u, hu, hu1⟩ := ed
      have hqd : H.q ∣ ordCompl[H.d] H.condN := Nat.dvd_ordCompl_of_dvd_not_dvd H.q_dvd_condN
        (fun hh => H.q_ne_d ((Nat.prime_dvd_prime_iff_eq hd hq).1 hh).symm)
      refine ⟨?_, u, hu, ?_⟩
      · change jacobiSym _ _ * jacobiSym _ _ = 0
        rw [jac_self _ hd.one_lt, zero_mul]
      · change jacobiSym _ _ * jacobiSym _ _ = -1
        rw [hu1, jacobi_congr (hu.of_dvd hqd)]
        simp
    · obtain rfl := (Nat.prime_dvd_prime_iff_eq hp hq).1 h
      obtain ⟨u, hu, hu1⟩ := eq
      have hqd : H.d ∣ ordCompl[H.q] H.condN := Nat.dvd_ordCompl_of_dvd_not_dvd H.d_dvd_condN
        (fun hh => H.q_ne_d ((Nat.prime_dvd_prime_iff_eq hq hd).1 hh))
      refine ⟨?_, u, hu, ?_⟩
      · change jacobiSym _ _ * jacobiSym _ _ = 0
        rw [jac_self _ hq.one_lt, mul_zero]
      · change jacobiSym _ _ * jacobiSym _ _ = -1
        rw [hu1, jacobi_congr (hu.of_dvd hqd)]
        simp
end UpperTheory.GL
