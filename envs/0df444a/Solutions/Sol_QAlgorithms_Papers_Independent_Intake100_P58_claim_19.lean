-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intake100.P58.claim_19
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T11:10:20.342701+00:00
-- url     : https://prove2.me/submissions/5b883b01-6d1c-417b-b916-9e3db42c43c6

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P58
noncomputable section

open scoped BigOperators Classical

namespace QAlgorithms.Papers.Independent.Intake100.P58

open Accepted

variable {R : Type*} [CommRing R] {k : ℕ}

theorem AuxC19_vNat_basis (P : NonsplitParameters R k) (l : ℕ) (h : l < k) :
    vNat P l = vBasis P ⟨l, h⟩ := by simp [vNat, h]

theorem AuxC19_Yv (P : NonsplitParameters R k) (s : ℕ) (h : s + 1 < k) :
    Yv P (vNat P s) = vNat P (s + 1) := by
  rw [AuxC19_vNat_basis P s (by omega), AuxC19_vNat_basis P (s+1) h]
  unfold Yv; rw [Module.Basis.constr_basis]; simp [h]

theorem AuxC19_pow (P : NonsplitParameters R k) (s : ℕ) (h : s < k) :
    (Yv P ^ s) (vNat P 0) = vNat P s := by
  induction s with
  | zero => simp
  | succ n ih => rw [pow_succ', Module.End.mul_apply, ih (by omega), AuxC19_Yv P n h]

theorem AuxC19_ov_nat (P : NonsplitParameters R k) (s : ℕ) (h : s < k) :
    orbitVector P (s : ℤ) = vNat P s := by
  simp [orbitVector, AuxC19_pow P s h]

theorem AuxC19_inv (P : NonsplitParameters R k) (s : ℤ) (h : s < k) :
    YvInv P (orbitVector P s) = orbitVector P (s - 1) := by
  rcases lt_or_ge 0 s with hs | hs
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, s = (n : ℤ) + 1 := ⟨(s - 1).toNat, by omega⟩
    have hn : n + 1 < k := by omega
    rw [show (n : ℤ) + 1 = ((n + 1 : ℕ) : ℤ) by push_cast; ring, AuxC19_ov_nat P _ hn,
      show ((n + 1 : ℕ) : ℤ) - 1 = (n : ℤ) by push_cast; ring, AuxC19_ov_nat P n (by omega),
      AuxC19_vNat_basis P _ hn]
    unfold YvInv; rw [Module.Basis.constr_basis]; simp
  · obtain ⟨m, rfl⟩ : ∃ m : ℕ, s = -(m : ℤ) := ⟨(-s).toNat, by omega⟩
    have h1 : orbitVector P (-(m : ℤ)) = (YvInv P ^ m) (vNat P 0) := by
      rcases Nat.eq_zero_or_pos m with h0 | h0
      · subst h0; simp [orbitVector]
      · simp [orbitVector]; intro h; omega
    have h2 : orbitVector P (-(m : ℤ) - 1) = (YvInv P ^ (m + 1)) (vNat P 0) := by
      simp only [orbitVector, show ¬ (0 ≤ -(m : ℤ) - 1) by omega, if_false]
      congr 2; omega
    rw [h1, h2, pow_succ', Module.End.mul_apply]

/-- Sum S l. -/
def AuxC19_S (P : NonsplitParameters R k) (l : ℕ) : CompanionModule P :=
  ∑ i ∈ Finset.Icc 1 l, (aAt P (l+1-i) • orbitVector P (1-(i : ℤ)) -
          orbitVector P ((l : ℤ)-2*(i : ℤ)+2))

theorem AuxC19_S_range (P : NonsplitParameters R k) (l : ℕ) :
    AuxC19_S P l = ∑ j ∈ Finset.range l, (aAt P (l-j) • orbitVector P (-(j : ℤ)) -
          orbitVector P ((l : ℤ)-2*(j : ℤ))) := by
  unfold AuxC19_S
  rw [show Finset.Icc 1 l = Finset.Ico 1 (l + 1) by ext x; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega, Finset.sum_Ico_eq_sum_range]
  refine Finset.sum_congr (by simp) fun j _ => ?_
  rw [show l + 1 - (1 + j) = l - j by omega]
  rw [show (1:ℤ) - ((1+j : ℕ):ℤ) = -(j:ℤ) by push_cast; ring,
    show (l:ℤ) - 2*((1+j:ℕ):ℤ) + 2 = l - 2*j by push_cast; ring]

theorem AuxC19_x (P : NonsplitParameters R k) :
    ∀ l, l < k → xColumn P l = (↑P.lam⁻¹ : R) • orbitVector P (-(l : ℤ)) +
      skeinDelta P • AuxC19_S P l + skeinDelta P • orbitVector P (l : ℤ) -
      (skeinDelta P * aAt P l) • orbitVector P 0 := by
  intro l
  induction l using Nat.strong_induction_on with
  | _ l ih =>
  intro hl
  match l, ih, hl with
  | 0, _, hl =>
    have hg := P.ground
    have ha : aAt P 0 = P.loop ⟨0, P.positive⟩ := by simp [aAt, hl]
    have : (P.lam : R) = ↑P.lam⁻¹ + skeinDelta P - skeinDelta P * aAt P 0 := by
      rw [ha]; unfold skeinDelta; linear_combination hg
    simp only [xColumn, AuxC19_S, Finset.Icc_self, Nat.cast_zero, neg_zero]
    have h0 : orbitVector P 0 = vNat P 0 := by simpa using AuxC19_ov_nat P 0 hl
    rw [h0, this]
    simp; module
  | 1, _, hl =>
    simp only [xColumn, AuxC19_S, Finset.Icc_self, Finset.sum_singleton]
    rw [← AuxC19_ov_nat P 0 (by omega), Nat.cast_zero, AuxC19_inv P 0 (by omega)]
    norm_num
    module
  | n + 2, ih, hl =>
    have ih1 := ih (n + 1) (by omega) (by omega)
    simp only [xColumn]
    rw [ih1, ← AuxC19_ov_nat P n (by omega),
      ← (show orbitVector P 0 = vNat P 0 by simpa using AuxC19_ov_nat P 0 (by omega)),
      AuxC19_inv P 0 (by omega)]
    simp only [map_add, map_sub, map_smul]
    rw [AuxC19_inv P _ (by omega), AuxC19_inv P _ (by omega), AuxC19_inv P _ (by omega)]
    rw [AuxC19_S_range, AuxC19_S_range, map_sum, Finset.sum_range_succ' _ (n + 1)]
    have hsum : ∑ j ∈ Finset.range (n + 1), YvInv P (aAt P (n + 1 - j) • orbitVector P (-(j : ℤ)) -
        orbitVector P (((n + 1 : ℕ) : ℤ) - 2 * (j : ℤ))) =
        ∑ j ∈ Finset.range (n + 1), (aAt P (n + 2 - (j + 1)) • orbitVector P (-((j + 1 : ℕ) : ℤ)) -
          orbitVector P (((n + 2 : ℕ) : ℤ) - 2 * ((j + 1 : ℕ) : ℤ))) := by
      refine Finset.sum_congr rfl fun j hj => ?_
      have hj' := Finset.mem_range.mp hj
      rw [map_sub, map_smul, AuxC19_inv P _ (by omega), AuxC19_inv P _ (by push_cast; omega),
        show n + 2 - (j + 1) = n + 1 - j by omega]
      congr 2 <;> push_cast <;> ring
    rw [hsum]
    simp only [Nat.cast_zero, neg_zero, mul_zero, sub_zero, Nat.sub_zero]
    have e1 : (-((n + 1 : ℕ) : ℤ) - 1) = -((n + 2 : ℕ) : ℤ) := by push_cast; ring
    have e2 : ((n + 1 : ℕ) : ℤ) - 1 = (n : ℤ) := by push_cast; ring
    rw [e1, e2]
    module

theorem _root_.solution (P : NonsplitParameters R k) (hdelta : RegularDelta P) :
    ∀ l : Fin k, Wv P (orbitVector P (l.val : ℤ)) =
      (↑P.lam⁻¹ : R) • orbitVector P (-(l.val : ℤ)) +
      skeinDelta P • (∑ i ∈ Finset.Icc 1 l.val,
        (aAt P (l.val+1-i) • orbitVector P (1-(i : ℤ)) -
          orbitVector P ((l.val : ℤ)-2*(i : ℤ)+2))) := by
  intro ⟨l, hl⟩
  have hx := AuxC19_x P l hl
  have hS : AuxC19_S P l = ∑ i ∈ Finset.Icc 1 l,
        (aAt P (l+1-i) • orbitVector P (1-(i : ℤ)) -
          orbitVector P ((l : ℤ)-2*(i : ℤ)+2)) := rfl
  have ha : aAt P l = P.loop ⟨l, hl⟩ := by simp [aAt, hl]
  simp only [Wv, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    Module.End.one_apply]
  rw [AuxC19_ov_nat P l hl, AuxC19_vNat_basis P l hl]
  have hX : Xv P (vBasis P ⟨l, hl⟩) = xColumn P l := by simp [Xv]
  have hE : Ev P (vBasis P ⟨l, hl⟩) = P.loop ⟨l, hl⟩ • vNat P 0 := by simp [Ev]
  rw [hX, hE, hx, ← hS, ← ha, AuxC19_ov_nat P l hl, AuxC19_vNat_basis P l hl,
    ← AuxC19_ov_nat P 0 (by omega), Nat.cast_zero]
  module

end QAlgorithms.Papers.Independent.Intake100.P58

end
