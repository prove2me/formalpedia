-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_FibreCut_proof_03cffe778f86
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T06:06:46.832075+00:00
-- url     : https://prove2.me/submissions/463d67b7-9b92-4c66-b690-4ed4ad99ac2f

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsFibreCut
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PFibreCut
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_not_lt_of_mem_minimalPrimes_sup_span_cd90bad77275
import Theorems.Thm_GroundTheory_Arith_Abelian_Jacobian_exists_ringKrullDim_eq_trdeg
import Theorems.Thm_GroundTheory_Arith_Abelian_Jacobian_ringKrullDim_quotient_add_one_le
import Theorems.Thm_GroundTheory_Arith_Toric_IsRationalPolyhedral_inf


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Vertical
open MvPolynomial IsDedekindDomain
namespace GroundTheory.Heights₂.Heights.Vertical
namespace FibreCut
theorem _root_.solution (hAvoid : CodimOnePrimeAvoid.Statement) : FibreCut.Statement := by
  intro O _ _ n P W v hP hPC hW hWmax
  classical
  set vX : Ideal (MvPolynomial (Fin n) O) :=
    Ideal.map (C : O →+* MvPolynomial (Fin n) O) v.asIdeal with hvX
  have hWp : W.IsPrime := hW.isPrime
  have hPW : P ≤ W := le_sup_left.trans hW.le
  have hvW : vX ≤ W := le_sup_right.trans hW.le
  have hfin := (P ⊔ vX).finite_minimalPrimes_of_isNoetherianRing

  obtain ⟨h, hhQ, hhW⟩ : ∃ h, (∀ Q ∈ (P ⊔ vX).minimalPrimes, Q ≠ W → h ∈ Q) ∧ h ∉ W := by
    have hnot : ¬ (hfin.toFinset.erase W).inf id ≤ W := by
      rw [hWp.inf_le']
      rintro ⟨Q, hQs, hQW⟩
      obtain ⟨hQW', hQ⟩ := Finset.mem_erase.mp hQs
      rw [Set.Finite.mem_toFinset] at hQ
      exact hQW' (le_antisymm hQW (hW.2 ⟨hQ.isPrime, hQ.le⟩ hQW))
    obtain ⟨h, hh, hhW⟩ := SetLike.not_le_iff_exists.mp hnot
    exact ⟨h, fun Q hQ hQW => Finset.inf_le (f := id)
      (Finset.mem_erase.mpr ⟨hQW, hfin.mem_toFinset.mpr hQ⟩) hh, hhW⟩

  have hvmax : v.asIdeal.IsMaximal := v.isPrime.isMaximal v.ne_bot
  have hWC : W.comap (C : O →+* MvPolynomial (Fin n) O) = v.asIdeal :=
    (hvmax.eq_of_le (Ideal.comap_ne_top _ hWp.ne_top) (Ideal.map_le_iff_le_comap.mp hvW)).symm
  have : W.LiesOver v.asIdeal := ⟨hWC.symm⟩
  let _ : Field (O ⧸ v.asIdeal) := Ideal.Quotient.field _
  have hBnf : ¬ IsField (MvPolynomial (Fin n) O ⧸ W) :=
    fun hf => hWmax (Ideal.Quotient.maximal_of_isField W hf)
  obtain ⟨I, hIbot, hItop⟩ := Ring.not_isField_iff_exists_ideal_bot_lt_and_lt_top.mp hBnf
  have hdim1 : 1 ≤ ringKrullDim (MvPolynomial (Fin n) O ⧸ W) := by
    have : Nontrivial (_ ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hItop.ne
    have h2 := GroundTheory.Arith.Abelian.Jacobian.ringKrullDim_quotient_add_one_le I hIbot.ne'
    have h0 := ringKrullDim_nonneg_of_nontrivial (R := (MvPolynomial (Fin n) O ⧸ W) ⧸ I)
    calc (1 : WithBot ℕ∞) = 0 + 1 := by simp
      _ ≤ ringKrullDim ((MvPolynomial (Fin n) O ⧸ W) ⧸ I) + 1 := add_le_add h0 le_rfl
      _ ≤ _ := h2
  obtain ⟨N₀, hN₀, hhN₀, hdimN₀⟩ := hAvoid (O ⧸ v.asIdeal) (MvPolynomial (Fin n) O ⧸ W)
    (Ideal.Quotient.mk W h) (by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]) hdim1

  set φ : MvPolynomial (Fin n) O →+* (MvPolynomial (Fin n) O ⧸ W) ⧸ N₀ :=
    (Ideal.Quotient.mk N₀).comp (Ideal.Quotient.mk W) with hφ
  have hφs : Function.Surjective φ :=
    Ideal.Quotient.mk_surjective.comp Ideal.Quotient.mk_surjective
  set N := RingHom.ker φ with hNdef
  have hNp : N.IsPrime := RingHom.ker_isPrime φ
  have hmemN : ∀ a, a ∈ N ↔ Ideal.Quotient.mk W a ∈ N₀ := fun a => by
    simp [N, φ, RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem]
  have hWN : W ≤ N := fun a ha => (hmemN a).mpr (by
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr ha]; exact N₀.zero_mem)
  have hhN : h ∉ N := fun hh => hhN₀ ((hmemN h).mp hh)
  have hdimN : ringKrullDim (MvPolynomial (Fin n) O ⧸ N) + 1 =
      ringKrullDim (MvPolynomial (Fin n) O ⧸ W) := by
    rw [ringKrullDim_eq_of_ringEquiv (RingHom.quotientKerEquivOfSurjective hφs)]
    exact hdimN₀
  have hNW : ¬ N ≤ W := by
    intro hle
    have hN₀bot : N₀ = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
      exact Ideal.mem_bot.mpr (Ideal.Quotient.eq_zero_iff_mem.mpr (hle ((hmemN a).mpr hx)))
    subst hN₀bot
    rw [ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot _)] at hdimN₀
    obtain ⟨m, hm, -⟩ := GroundTheory.Arith.Abelian.Jacobian.exists_ringKrullDim_eq_trdeg
      (k := O ⧸ v.asIdeal) (A := MvPolynomial (Fin n) O ⧸ W)
    rw [hm] at hdimN₀
    have : ((m + 1 : ℕ) : WithBot ℕ∞) = (m : WithBot ℕ∞) := by push_cast; exact hdimN₀
    have : m + 1 = m := by exact_mod_cast this
    omega

  have hNQ : ∀ Q ∈ (P ⊔ vX).minimalPrimes, ¬ N ≤ Q := fun Q hQ hle =>
    hNW (hle.trans (hQ.2 ⟨hWp, hW.le⟩ (hWN.trans hle)))
  obtain ⟨f, hfN, hfQ⟩ : ∃ f ∈ N, ∀ Q ∈ (P ⊔ vX).minimalPrimes, f ∉ Q := by
    have hns : ¬ ((N : Set (MvPolynomial (Fin n) O)) ⊆
        ⋃ Q ∈ (↑hfin.toFinset : Set (Ideal (MvPolynomial (Fin n) O))), ((id Q : Ideal _) : Set _)) := by
      rw [Ideal.subset_union_prime (f := id) ⊥ ⊥
        (fun Q hQ _ _ => (hfin.mem_toFinset.mp hQ).isPrime)]
      rintro ⟨Q, hQ, hle⟩
      exact hNQ Q (hfin.mem_toFinset.mp hQ) hle
    obtain ⟨f, hfN, hf⟩ := Set.not_subset.mp hns
    refine ⟨f, hfN, fun Q hQ hfQ => hf ?_⟩
    exact Set.mem_biUnion (Finset.mem_coe.mpr (hfin.mem_toFinset.mpr hQ)) hfQ
  have hfW : f ∉ W := hfQ W hW
  have hfP : f ∉ P := fun hf => hfW (hPW hf)

  have hPfN : P ⊔ Ideal.span {f} ≤ N :=
    sup_le (hPW.trans hWN) ((Ideal.span_singleton_le_iff_mem _).mpr hfN)
  obtain ⟨P', hP', hP'N⟩ := Ideal.exists_minimalPrimes_le hPfN
  have hP'p : P'.IsPrime := hP'.isPrime
  have hPP' : P ≤ P' := le_sup_left.trans hP'.le
  have hfP' : f ∈ P' := hP'.le (Ideal.mem_sup_right (Ideal.mem_span_singleton_self f))
  have hQN : ∀ Q ∈ (P ⊔ vX).minimalPrimes, Q ≤ N → Q = W := fun Q hQ hle => by
    by_contra hne
    exact hhN (hle (hhQ Q hQ hne))
  have hPltW : P < W := lt_of_le_of_ne hPW fun hPW' => v.ne_bot (by
    rw [eq_bot_iff, ← hPC, hPW']
    exact Ideal.map_le_iff_le_comap.mp hvW)
  have hvP' : ¬ vX ≤ P' := by
    intro hle
    obtain ⟨Q, hQ, hQP'⟩ := Ideal.exists_minimalPrimes_le (sup_le hPP' hle)
    rw [hQN Q hQ (hQP'.trans hP'N)] at hQP'
    rcases hQP'.lt_or_eq with hlt | heq
    · exact not_lt_of_mem_minimalPrimes_sup_span hPltW hP' hlt
    · exact hfW (heq ▸ hfP')
  have hP'C : P'.comap (C : O →+* MvPolynomial (Fin n) O) = ⊥ := by
    by_contra hne
    have hmax : (P'.comap (C : O →+* MvPolynomial (Fin n) O)).IsMaximal :=
      Ideal.IsPrime.isMaximal inferInstance hne
    have heq : P'.comap (C : O →+* MvPolynomial (Fin n) O) = N.comap C :=
      hmax.eq_of_le (Ideal.comap_ne_top _ hNp.ne_top) (Ideal.comap_mono hP'N)
    apply hvP'
    rw [hvX, Ideal.map_le_iff_le_comap, heq]
    exact Ideal.map_le_iff_le_comap.mp (hvW.trans hWN)

  obtain ⟨W', hW', hW'N⟩ := Ideal.exists_minimalPrimes_le
    (sup_le hP'N (hvW.trans hWN) : P' ⊔ vX ≤ N)
  have : W'.IsPrime := hW'.isPrime
  have hWW' : W ≤ W' := by
    obtain ⟨Q, hQ, hQW'⟩ := Ideal.exists_minimalPrimes_le
      (sup_le (hPP'.trans (le_sup_left.trans hW'.le)) (le_sup_right.trans hW'.le) : P ⊔ vX ≤ W')
    rw [← hQN Q hQ (hQW'.trans hW'N)]
    exact hQW'
  have hfW' : f ∈ W' := hW'.le (Ideal.mem_sup_left hfP')
  refine ⟨P', W', f, hfP, hP', hP'C, hW', le_antisymm ?_ ?_⟩
  · have hne : W'.map (Ideal.Quotient.mk W) ≠ ⊥ := by
      intro hb
      apply hfW
      have hm : Ideal.Quotient.mk W f ∈ W'.map (Ideal.Quotient.mk W) := Ideal.mem_map_of_mem _ hfW'
      rw [hb, Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem] at hm
      exact hm
    have h2 := GroundTheory.Arith.Abelian.Jacobian.ringKrullDim_quotient_add_one_le _ hne
    rwa [ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hWW')] at h2
  · rw [← hdimN]
    exact add_le_add (ringKrullDim_le_of_surjective (Ideal.Quotient.factor hW'N)
      (Ideal.Quotient.factor_surjective hW'N)) le_rfl
end FibreCut
end GroundTheory.Heights₂.Heights.Vertical
