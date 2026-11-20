-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intake100.P58.companion_inverse_recurrence_bases
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T11:13:59.414199+00:00
-- url     : https://prove2.me/submissions/0ccb4d4c-17c2-4cd2-919c-5475344f9730

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P58
noncomputable section

open scoped BigOperators Classical

namespace QAlgorithms.Papers.Independent.Intake100.P58

open Accepted

variable {R : Type*} [CommRing R] {k : ℕ}
theorem AuxCI_vNat_basis (P : NonsplitParameters R k) (l : ℕ) (h : l < k) :
    vNat P l = vBasis P ⟨l, h⟩ := by simp [vNat, h]

theorem AuxCI_Yv (P : NonsplitParameters R k) (s : ℕ) (h : s + 1 < k) :
    Yv P (vNat P s) = vNat P (s + 1) := by
  rw [AuxCI_vNat_basis P s (by omega), AuxCI_vNat_basis P (s+1) h]
  unfold Yv; rw [Module.Basis.constr_basis]; simp [h]

theorem AuxCI_pow (P : NonsplitParameters R k) (s : ℕ) (h : s < k) :
    (Yv P ^ s) (vNat P 0) = vNat P s := by
  induction s with
  | zero => simp
  | succ n ih => rw [pow_succ', Module.End.mul_apply, ih (by omega), AuxCI_Yv P n h]

theorem AuxCI_ov_nat (P : NonsplitParameters R k) (s : ℕ) (h : s < k) :
    orbitVector P (s : ℤ) = vNat P s := by
  simp [orbitVector, AuxCI_pow P s h]

theorem AuxCI_Ybasis (P : NonsplitParameters R k) (i : Fin k) :
    Yv P (vBasis P i) = if h : i.val + 1 < k then vBasis P ⟨i.val+1, h⟩
      else ∑ j : Fin k, P.coeff j • vBasis P j := by
  unfold Yv; rw [Module.Basis.constr_basis]

theorem AuxCI_Yibasis (P : NonsplitParameters R k) (i : Fin k) :
    YvInv P (vBasis P i) = if i.val = 0 then
      -(↑P.constant⁻¹ : R) • (∑ j : Fin k, qAt P (j.val+1) • vBasis P j)
    else vNat P (i.val-1) := by
  unfold YvInv; rw [Module.Basis.constr_basis]

theorem AuxCI_q (P : NonsplitParameters R k) (i : ℕ) (h : i < k) : qAt P i = P.coeff ⟨i, h⟩ := by
  simp [qAt, h]

theorem AuxCI_qk (P : NonsplitParameters R k) : qAt P k = -1 := by simp [qAt]

theorem AuxCI_YYi (P : NonsplitParameters R k) : Yv P * YvInv P = 1 := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by have := P.positive; omega⟩
  refine (vBasis P).ext fun i => ?_
  rw [Module.End.mul_apply, Module.End.one_apply, AuxCI_Yibasis]
  split_ifs with hi
  · have hi0 : i = 0 := Fin.ext hi
    subst hi0
    have hc : P.coeff 0 = (P.constant : R) := P.constant_eq
    have hlast : Yv P (vBasis P (Fin.last n)) = ∑ j, P.coeff j • vBasis P j := by
      rw [AuxCI_Ybasis, dif_neg (by simp)]
    have hcs : ∀ j : Fin n, Yv P (vBasis P j.castSucc) = vBasis P j.succ := by
      intro j; rw [AuxCI_Ybasis, dif_pos (by simp)]; rfl
    have h2 : ∀ j : Fin n, qAt P (j + 1) = P.coeff j.succ := fun j => AuxCI_q P _ (by omega)
    have hsum : ∑ j : Fin (n+1), qAt P (j.val+1) • Yv P (vBasis P j) =
        -((P.constant : R) • vBasis P 0) := by
      rw [Fin.sum_univ_castSucc]
      simp only [hcs, hlast, Fin.val_castSucc, Fin.val_last, AuxCI_qk, h2]
      rw [Fin.sum_univ_succ (f := fun j => P.coeff j • vBasis P j), hc]
      module
    rw [map_smul, map_sum]
    simp only [map_smul]
    rw [hsum, smul_neg, smul_smul, neg_mul, Units.inv_mul, neg_smul, one_smul, neg_neg]
  · have hi2 := i.2
    obtain ⟨m, hm⟩ : ∃ m, i.val = m + 1 := ⟨i.val - 1, by omega⟩
    rw [hm, Nat.add_sub_cancel, AuxCI_vNat_basis P m (by omega), AuxCI_Ybasis, dif_pos (by simp; omega)]
    congr 1; ext; simp [hm]

theorem AuxCI_YiY (P : NonsplitParameters R k) : YvInv P * Yv P = 1 := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by have := P.positive; omega⟩
  refine (vBasis P).ext fun i => ?_
  rw [Module.End.mul_apply, Module.End.one_apply, AuxCI_Ybasis]
  split_ifs with hi
  · rw [AuxCI_Yibasis, if_neg (by simp), Nat.add_sub_cancel, AuxCI_vNat_basis P _ (by omega)]
  · have hil : i = Fin.last n := Fin.ext (by simp; omega)
    subst hil
    rw [map_sum, Fin.sum_univ_succ]
    simp only [map_smul, AuxCI_Yibasis, Fin.val_zero, if_true, Fin.val_succ,
      show ∀ j : ℕ, j + 1 ≠ 0 from fun j => by omega, if_false, Nat.add_sub_cancel]
    rw [Fin.sum_univ_castSucc (f := fun j : Fin (n+1) => qAt P (j.val+1) • vBasis P j)]
    simp only [Fin.val_castSucc, Fin.val_last, AuxCI_qk]
    have h2 : ∀ j : Fin n, qAt P (j + 1) = P.coeff j.succ := fun j => AuxCI_q P _ (by omega)
    have h3 : ∀ j : Fin n, vNat P (j : ℕ) = vBasis P j.castSucc := fun j =>
      AuxCI_vNat_basis P _ (by omega)
    simp only [h2, h3]
    have hc := P.constant_eq
    simp only [Fin.zero_eta] at hc ⊢
    rw [smul_smul, mul_neg, hc, Units.mul_inv]
    module


theorem AuxCI_Q (P : NonsplitParameters R k) :
    (∑ l ∈ Finset.range (k+1), qAt P l • Yv P ^ l) = 0 := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by have := P.positive; omega⟩
  set Q := ∑ l ∈ Finset.range (n+1+1), qAt P l • Yv P ^ l with hQ
  have hcomm : ∀ j : ℕ, Q * Yv P ^ j = Yv P ^ j * Q := by
    intro j
    rw [hQ, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [smul_mul_assoc, mul_smul_comm, ← pow_add, ← pow_add, Nat.add_comm l j]
  have h0 : Q (vNat P 0) = 0 := by
    rw [hQ, LinearMap.sum_apply, Finset.sum_range_succ]
    simp only [LinearMap.smul_apply, AuxCI_qk]
    have hlt : ∀ l ∈ Finset.range (n+1), qAt P l • (Yv P ^ l) (vNat P 0) =
        qAt P l • vNat P l := fun l hl => by
      rw [AuxCI_pow P l (Finset.mem_range.mp hl)]
    rw [Finset.sum_congr rfl hlt, Finset.sum_range (fun l => qAt P l • vNat P l), pow_succ',
      Module.End.mul_apply, AuxCI_pow P n (by omega), AuxCI_vNat_basis P n (by omega)]
    have hl : (⟨n, by omega⟩ : Fin (n+1)) = Fin.last n := rfl
    rw [hl, AuxCI_Ybasis, dif_neg (by simp)]
    have : ∀ i : Fin (n+1), qAt P i • vNat P i = P.coeff i • vBasis P i := fun i => by
      rw [AuxCI_q P _ i.2, AuxCI_vNat_basis P _ i.2]
    simp only [this]
    module
  refine (vBasis P).ext fun j => ?_
  rw [LinearMap.zero_apply, ← AuxCI_vNat_basis P j j.2, ← AuxCI_pow P j j.2, ← Module.End.mul_apply,
    hcomm, Module.End.mul_apply, h0, map_zero]

/-- The unit. -/
def AuxCI_U (P : NonsplitParameters R k) : (Module.End R (CompanionModule P))ˣ :=
  ⟨Yv P, YvInv P, AuxCI_YYi P, AuxCI_YiY P⟩

theorem AuxCI_ovU (P : NonsplitParameters R k) (s : ℤ) :
    orbitVector P s = ((AuxCI_U P ^ s : (Module.End R (CompanionModule P))ˣ) : Module.End R _) (vNat P 0) := by
  rcases le_or_gt 0 s with hs | hs
  · obtain ⟨m, rfl⟩ : ∃ m : ℕ, s = m := ⟨s.toNat, by omega⟩
    rw [zpow_natCast, Units.val_pow_eq_pow_val]
    simp [orbitVector]; rfl
  · obtain ⟨m, rfl⟩ : ∃ m : ℕ, s = -((m + 1 : ℕ) : ℤ) := ⟨(-s).toNat - 1, by omega⟩
    rw [zpow_neg, zpow_natCast, ← inv_pow, Units.val_pow_eq_pow_val]
    simp only [orbitVector, show ¬ (0 ≤ -((m + 1 : ℕ) : ℤ)) by omega, if_false]
    rw [show (-(-((m + 1 : ℕ) : ℤ))).toNat = m + 1 by omega]
    rfl

theorem _root_.solution (P : NonsplitParameters R k) (hdelta : RegularDelta P) :
    Yv P * YvInv P = 1 ∧ YvInv P * Yv P = 1 ∧
    (∀ i : Fin k, 1 ≤ i.val → YvInv P (vNat P i.val) = vNat P (i.val-1)) ∧
    YvInv P (vNat P 0) =
      -(↑P.constant⁻¹ : R) • (∑ i : Fin k, qAt P (i.val+1) • vNat P i.val) ∧
    (∀ i : Fin k, orbitVector P (i.val : ℤ) = vNat P i.val) ∧
    (∀ i : ℤ, (∑ l ∈ Finset.range (k+1), qAt P l • (Yv P ^ l) (orbitVector P i)) = 0) ∧
    (∀ l : ℤ, ∃ b : Module.Basis (Fin k) R (CompanionModule P),
      ∀ i : Fin k, b i = orbitVector P (l + (i.val : ℤ))) := by
  have hk := P.positive
  have hvb : ∀ i : Fin k, vNat P i.val = vBasis P i := fun i => AuxCI_vNat_basis P _ i.2
  refine ⟨AuxCI_YYi P, AuxCI_YiY P, ?_, ?_, fun i => AuxCI_ov_nat P _ i.2, ?_, ?_⟩
  · intro i hi
    rw [hvb, AuxCI_Yibasis, if_neg (by omega)]
  · rw [AuxCI_vNat_basis P 0 hk, AuxCI_Yibasis, if_pos rfl]
    simp only [hvb]
  · intro i
    have := congrArg (fun F : Module.End R (CompanionModule P) => F (orbitVector P i)) (AuxCI_Q P)
    simpa [LinearMap.sum_apply] using this
  · intro l
    refine ⟨(vBasis P).map (LinearMap.GeneralLinearGroup.generalLinearEquiv R _ (AuxCI_U P ^ l)),
      fun i => ?_⟩
    rw [Module.Basis.map_apply, AuxCI_ovU, zpow_add, Units.val_mul, Module.End.mul_apply,
      ← AuxCI_ovU, AuxCI_ov_nat P _ i.2, hvb]
    rfl

end QAlgorithms.Papers.Independent.Intake100.P58

end
