-- Prove2me | solution 1 for UpperTheory.Ram.isCond_condN
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:48:49.314806+00:00
-- url     : https://prove2.me/submissions/1d027454-70f7-45b1-b70b-9df9e884474e

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataHost
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_RealCyclotomicTwoPower
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_HostFacts
import Definitions.Def_Development_AutomorphicArithmetic_PrimeDiscriminants_CycImage
import Definitions.Def_Development_AutomorphicArithmetic_PrimeDiscriminants_RamDiscr
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_RamifiedDiscriminants_IsCond
import Theorems.Thm_Formalism_FrobeniusOrbits_Cond_emb
import Theorems.Thm_Formalism_FrobeniusOrbits_Cond_z_spec
import Theorems.Thm_Formalism_FrobeniusOrbits_Group_key
import Theorems.Thm_Formalism_FrobeniusOrbits_ThickOrbit_key
import Theorems.Thm_Formalism_HC_D7_exists_sign
import Theorems.Thm_Formalism_HC_D7_jac_congr
import Theorems.Thm_Formalism_HC_Der_emb_art
import Theorems.Thm_Formalism_HC_Der_exists_art_iod
import Theorems.Thm_Formalism_HC_Der_exists_unit_modEq
import Theorems.Thm_Formalism_HC_Der_tauN_root
import Theorems.Thm_Formalism_HC_Frame_iod_ne_one
import Theorems.Thm_Formalism_HC_HostRaw_coprime_QSd_q
import Theorems.Thm_Formalism_HC_HostRaw_dvd_condN_iff
import Theorems.Thm_Formalism_HC_HostRaw_image_mem_of_roots
import Theorems.Thm_Formalism_HC_HostRaw_q_dvd_condN
import Theorems.Thm_Formalism_HC_HostRaw_q_mod_four

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open NumberField
namespace UpperTheory.Ram
open Formalism.L2.Host Formalism.HC Formalism.HC.Der Formalism.FrobeniusOrbits
private theorem exists_aut_pow (N : ℕ) (hN : 0 < N) (u : ℕ) (hu : u.Coprime N) :
    ∃ s : Qb ≃ₐ[ℚ] Qb, ∀ z ∈ mus N, s z = z ^ u := by
  haveI : NeZero N := ⟨hN.ne'⟩
  obtain ⟨w, hw⟩ : ∃ w : Qb, IsPrimitiveRoot w N := HasEnoughRootsOfUnity.exists_primitiveRoot Qb N
  have hw' : IsPrimitiveRoot (w ^ u) N := hw.pow_of_coprime u hu
  have hc : IsConjRoot ℚ (w ^ u) w := by
    unfold IsConjRoot
    rw [← Polynomial.cyclotomic_eq_minpoly_rat hw hN, ← Polynomial.cyclotomic_eq_minpoly_rat hw' hN]
  haveI : IsAlgClosure ℚ Qb := AlgebraicClosure.instIsAlgClosure ℚ
  haveI : Normal ℚ Qb := IsAlgClosure.normal ℚ Qb
  obtain ⟨s, hs⟩ := hc.exists_algEquiv
  refine ⟨s, fun z hz => ?_⟩
  obtain ⟨i, -, rfl⟩ := hw.eq_pow_of_pow_eq_one hz
  rw [map_pow, hs, ← pow_mul, ← pow_mul, mul_comm]
private theorem exists_aut_fix (N M : ℕ) (hN : 0 < N) (hM : 0 < M) (u : ℕ) (hu : u.Coprime N)
    (hu1 : u ≡ 1 [MOD M]) :
    ∃ s : Qb ≃ₐ[ℚ] Qb, (∀ z ∈ mus N, s z = z ^ u) ∧ ∀ x ∈ cycQ M, s x = x := by
  have huM : u.Coprime M := by
    unfold Nat.Coprime
    rw [hu1.gcd_eq, Nat.gcd_one_left]
  obtain ⟨s, hs⟩ := exists_aut_pow (N * M) (Nat.mul_pos hN hM) u (Nat.Coprime.mul_right hu huM)
  refine ⟨s, fun z hz => hs z ?_, fun x hx => ?_⟩
  · show z ^ (N * M) = 1
    rw [pow_mul, show z ^ N = 1 from hz, one_pow]
  · unfold cycQ at hx
    induction hx using IntermediateField.adjoin_induction with
    | mem z hz =>
      have hz' : z ^ M = 1 := hz
      rw [hs z (by show z ^ (N * M) = 1; rw [mul_comm, pow_mul, hz', one_pow]),
        pow_eq_pow_of_modEq hu1 hz', pow_one]
    | algebraMap r => exact s.commutes r
    | add a b _ _ ha hb => rw [map_add, ha, hb]
    | inv a _ ha => rw [map_inv₀, ha]
    | mul a b _ _ ha hb => rw [map_mul, ha, hb]
private theorem aut_art {φ : Frame} (H : HostRaw φ) (j : H.E →ₐ[ℚ] Qb) (u : (ZMod H.condN)ˣ) (s : Qb ≃ₐ[ℚ] Qb)
    (hs : ∀ z ∈ mus H.condN, s z = z ^ (u : ZMod H.condN).val) (x : H.E) :
    s (j x) = j (H.gal.symm (H.art u) x) := by
  let _ : Algebra H.E (Cond.Cyc H.condN) := (emb H).toRingHom.toAlgebra
  have : IsScalarTower ℚ H.E (Cond.Cyc H.condN) := IsScalarTower.of_algebraMap_eq fun x => ((emb H).commutes x).symm
  have : Algebra.IsAlgebraic H.E (Cond.Cyc H.condN) := Algebra.IsAlgebraic.tower_top (K := ℚ) H.E
  let _ : Algebra H.E Qb := j.toRingHom.toAlgebra
  let Ψ0 : Cond.Cyc H.condN →ₐ[H.E] Qb := IsAlgClosed.lift
  let Ψ : Cond.Cyc H.condN →+* Qb := Ψ0.toRingHom
  have h1 : ∀ y, Ψ (emb H y) = j y := fun y => Ψ0.commutes y
  have key : (Ψ.comp (tauN H.condN u : Cond.Cyc H.condN →+* Cond.Cyc H.condN)).toRatAlgHom =
      ((s : Qb →+* Qb).comp Ψ).toRatAlgHom := by
    refine AlgHom.ext_of_adjoin_eq_top
      (IsCyclotomicExtension.adjoin_primitive_root_eq_top (Cond.z_spec H.condN)) ?_
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    show Ψ (tauN H.condN u (Cond.z H.condN)) = s (Ψ (Cond.z H.condN))
    have hz := (Cond.z_spec H.condN).pow_eq_one
    rw [tauN_root H.condN _ _ hz, map_pow, hs _ (show _ ^ H.condN = 1 by rw [← map_pow, hz, map_one])]
  rw [← h1, ← h1, emb_art]
  exact (DFunLike.congr_fun key (emb H x)).symm
private theorem exists_exact {R : Formalism.BasicNotions.Ranks} (H : Formalism.BasicNotions.Host R) {l : ℕ} (hl : l.Prime) (hd : l ∣ H.condN) :
    ∃ u : (ZMod H.condN)ˣ, (u : ZMod H.condN).val ≡ 1 [MOD H.condN / l] ∧ H.art u ≠ 1 := by
  rcases (H.toHostRaw.dvd_condN_iff hl).1 hd with h | rfl | rfl
  · exact H.QS_exact l hl h
  · have hN : H.condN = H.QS * H.d * H.q := mul_right_comm _ _ _
    obtain ⟨b, hb, hj⟩ := D7.exists_sign H.q_prime H.q_mod_four (-1)
    obtain ⟨n, hn1, hn2⟩ := Nat.chineseRemainder H.toHostRaw.coprime_QSd_q 1 b
    obtain ⟨u, hu⟩ := exists_unit_modEq (dvd_refl H.condN) n
      (hN ▸ Nat.Coprime.mul_right (hn1.gcd_eq.trans (Nat.coprime_one_left _)) (hn2.gcd_eq.trans hb))
    refine ⟨u, ?_, fun h3 => ?_⟩
    · rw [show H.condN / H.q = H.QS * H.d by rw [hN, Nat.mul_div_cancel _ hl.pos]]
      exact (hu.of_dvd ⟨H.q, hN⟩).trans hn1
    · have h4 := H.flPS u
      rw [h3, D7.jac_congr ((hu.of_dvd H.toHostRaw.q_dvd_condN).trans hn2), hj] at h4
      exact absurd h4 (show ¬ ((1 : ℤˣ) : ℤ) = ((-1 : ℤˣ) : ℤ) by decide)
  · obtain ⟨u, h1, h2⟩ := exists_art_iod H.toHostRaw
    refine ⟨u, ?_, fun h3 => R.toFrame.iod_ne_one (h2.symm.trans h3)⟩
    rwa [show H.condN / H.d = H.QS * H.q from Nat.mul_div_cancel _ hl.pos]
end UpperTheory.Ram
end

set_option autoImplicit false
open NumberField
namespace UpperTheory.Ram
theorem _root_.solution :
    ∀ {R : Formalism.BasicNotions.Ranks} (H : Formalism.BasicNotions.Host R) (j : H.E →ₐ[ℚ] Formalism.L2.Host.Qb),
      Formalism.L2.Host.IsCond j.fieldRange H.condN := by
  intro R H j
  have hN : 0 < H.condN := Nat.pos_of_ne_zero H.toHostRaw.condN_ne_zero
  refine ⟨?_, fun M hM hle => ?_⟩
  · rintro _ ⟨x, rfl⟩
    exact H.toHostRaw.image_mem_of_roots j.toRingHom (Formalism.L2.Host.cycQ H.condN).toSubfield
      (fun y hy => IntermediateField.subset_adjoin ℚ _ hy) x
  · by_contra hn
    obtain ⟨k, hk⟩ := Nat.gcd_dvd_left H.condN M
    have hk1 : k ≠ 1 := by
      rintro rfl
      rw [mul_one] at hk
      exact hn (hk ▸ Nat.gcd_dvd_right _ _)
    obtain ⟨l, hl, m, rfl⟩ := Nat.exists_prime_and_dvd hk1
    have hld : l ∣ H.condN := ⟨Nat.gcd H.condN M * m, hk.trans (by ring)⟩
    have hg : Nat.gcd H.condN M ∣ H.condN / l :=
      ⟨m, Nat.div_eq_of_eq_mul_right hl.pos (hk.trans (by ring))⟩
    obtain ⟨u, hu1, hu2⟩ := exists_exact H hl hld
    obtain ⟨n, hn1, hn2⟩ := Nat.chineseRemainder' (hu1.of_dvd hg)
    obtain ⟨s, hs1, hs2⟩ := exists_aut_fix H.condN M hN hM n
      (hn1.gcd_eq.trans (ZMod.val_coe_unit_coprime u)) hn2
    apply hu2
    rw [← H.gal.symm.map_eq_one_iff]
    refine AlgEquiv.ext fun x => j.injective ?_
    have h := aut_art H.toHostRaw j u s (fun z hz => by rw [hs1 z hz, pow_eq_pow_of_modEq hn1 hz]) x
    exact h.symm.trans (hs2 _ (hle ⟨x, rfl⟩))
end UpperTheory.Ram
