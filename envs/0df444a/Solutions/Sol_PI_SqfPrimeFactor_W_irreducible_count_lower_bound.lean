-- Prove2me | solution 1 for PI.SqfPrimeFactor.W.irreducible_count_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:29:05.211248+00:00
-- url     : https://prove2.me/submissions/4fb50475-151a-491b-9f05-f1c79df6d8d7

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreePrimeFactor_BigPrimes
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreePrimeFactor_IrreducibleCountLowerBound
import Theorems.Thm_PI_SqfPrimeFactor_W_irr_mem_monicDeg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Finset
noncomputable section
open PI PI.SqfPrimeFactor PI.SqfPrimeFactor.W
namespace PI.SqfPrimeFactor.W
theorem _root_.solution : IrrLower := by
  intro g p _ hp
  classical
  let _ : Fintype (GaloisField g p) := Fintype.ofFinite _
  have hp0 : p ≠ 0 := hp.ne_zero
  have hcardK : Fintype.card (GaloisField g p) = g ^ p := by
    rw [← Nat.card_eq_fintype_card]; exact GaloisField.card g p hp0
  have hfin : Module.finrank (ZMod g) (GaloisField g p) = p := GaloisField.finrank g hp0
  have hint : ∀ x : GaloisField g p, IsIntegral (ZMod g) x :=
    fun x => Algebra.IsIntegral.isIntegral x
  set A := (univ : Finset (GaloisField g p)).filter
    (fun x => x ∉ (algebraMap (ZMod g) (GaloisField g p)).range) with hA
  set B := (univ : Finset (GaloisField g p)).filter
    (fun x => x ∈ (algebraMap (ZMod g) (GaloisField g p)).range) with hB
  have hAB : B.card + A.card = g ^ p := by
    rw [hA, hB, card_filter_add_card_filter_not, card_univ, hcardK]
  have hBle : B.card ≤ g := by
    have hsub : B ⊆ (univ : Finset (ZMod g)).image (algebraMap (ZMod g) (GaloisField g p)) := by
      intro x hx
      rw [hB, mem_filter] at hx
      obtain ⟨y, rfl⟩ := hx.2
      exact mem_image_of_mem _ (mem_univ y)
    calc B.card ≤ _ := card_le_card hsub
      _ ≤ (univ : Finset (ZMod g)).card := card_image_le
      _ = g := by rw [card_univ, ZMod.card]
  have hdegA : ∀ x ∈ A, (minpoly (ZMod g) x).natDegree = p := by
    intro x hx
    rw [hA, mem_filter] at hx
    have hdvd := minpoly.degree_dvd (hint x)
    rw [hfin] at hdvd
    rcases (Nat.dvd_prime hp).1 hdvd with h | h
    · exact absurd (minpoly.natDegree_eq_one_iff.1 h) hx.2
    · exact h
  have himg : A.image (minpoly (ZMod g)) ⊆ irrDeg g p := by
    intro q hq
    rw [mem_image] at hq
    obtain ⟨x, hx, rfl⟩ := hq
    unfold irrDeg
    rw [mem_filter]
    exact ⟨irr_mem_monicDeg (minpoly.monic (hint x)) (hdegA x hx), minpoly.irreducible (hint x)⟩
  have hfib : ∀ q ∈ A.image (minpoly (ZMod g)),
      (A.filter (fun x => minpoly (ZMod g) x = q)).card ≤ p := by
    intro q hq
    obtain ⟨x0, hx0, rfl⟩ := mem_image.1 hq
    have hne : (minpoly (ZMod g) x0).map (algebraMap (ZMod g) (GaloisField g p)) ≠ 0 :=
      Polynomial.map_ne_zero (minpoly.ne_zero (hint x0))
    have hsub : A.filter (fun x => minpoly (ZMod g) x = minpoly (ZMod g) x0) ⊆
        ((minpoly (ZMod g) x0).map (algebraMap (ZMod g) (GaloisField g p))).roots.toFinset := by
      intro y hy
      rw [mem_filter] at hy
      rw [Multiset.mem_toFinset, mem_roots hne, IsRoot.def, eval_map_algebraMap, ← hy.2]
      exact minpoly.aeval _ _
    calc _ ≤ _ := card_le_card hsub
      _ ≤ _ := Multiset.toFinset_card_le _
      _ ≤ _ := card_roots' _
      _ = (minpoly (ZMod g) x0).natDegree := natDegree_map _
      _ = p := hdegA x0 hx0
  have hAle : A.card ≤ p * (A.image (minpoly (ZMod g))).card := card_le_mul_card_image A p hfib
  have hAle' : A.card ≤ p * (irrDeg g p).card :=
    hAle.trans (Nat.mul_le_mul_left _ (card_le_card himg))
  have hN : g ^ p ≤ p * (irrDeg g p).card + g := by omega
  have hR : ((g ^ p : ℕ) : ℝ) ≤ ((p * (irrDeg g p).card + g : ℕ) : ℝ) := by exact_mod_cast hN
  push_cast at hR
  linarith
end PI.SqfPrimeFactor.W
