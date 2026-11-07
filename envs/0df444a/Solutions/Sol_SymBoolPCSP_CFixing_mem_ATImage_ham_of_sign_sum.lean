-- Prove2me | solution 1 for SymBoolPCSP.CFixing.mem_ATImage_ham_of_sign_sum
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-11-06T09:10:51.076221+00:00
-- url     : https://prove2.me/submissions/b479c6af-b2d4-4fad-a34a-3cdf314e08fe

import Mathlib
import Definitions.Def_PCSPBLPAff_Symmetric_Setting
import Definitions.Def_SymBoolPCSP_CFixing_Basic
import Theorems.Thm_SymBoolPCSP_CFixing_mem_ATImage_of_mem_diffClosure

open PCSPBLPAff.Symmetric Finset
namespace SymBoolPCSP.CFixing

namespace Aux_mem_ATImage_ham_of_sign_sum

theorem hw_decide_mem {k : ℕ} (T : Finset (Fin k)) : hw (fun c => decide (c ∈ T)) = T.card := by
  unfold hw; congr 1; ext c; simp

theorem sum_boole_hw {k : ℕ} (x : Fin k → Bool) :
    ∑ c, (if x c then (1 : ℤ) else 0) = (hw x : ℤ) := by
  unfold hw; rw [Finset.sum_boole]

theorem exists_hw_eq {k w : ℕ} (hw' : w ≤ k) : ∃ x : Fin k → Bool, hw x = w := by
  obtain ⟨T, -, hT⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset (Fin k)))
    (n := w) (by simpa using hw')
  exact ⟨_, by rw [hw_decide_mem, hT]⟩

theorem ham_diffClosure {k : ℕ} {S : Set ℕ} {l l' : ℕ} (hl : l ∈ S) (hl1 : 1 ≤ l)
    (hlk : l + 1 ≤ k) (hl' : l' ∈ S) (hl'k : l' ≤ k) (z : Fin k → ℤ)
    (hz : ((l' : ℤ) - l) ∣ ∑ c, z c) :
    z ∈ AddSubgroup.closure {d : Fin k → ℤ | ∃ u ∈ Ham k S, ∃ v ∈ Ham k S,
        d = fun c => (if v c then 1 else 0) - (if u c then 1 else 0)} := by
  set H := AddSubgroup.closure {d : Fin k → ℤ | ∃ u ∈ Ham k S, ∃ v ∈ Ham k S,
        d = fun c => (if v c then 1 else 0) - (if u c then 1 else 0)} with hH
  have gen : ∀ u ∈ Ham k S, ∀ v ∈ Ham k S,
      (fun c => (if v c then (1 : ℤ) else 0) - (if u c then 1 else 0)) ∈ H :=
    fun u hu v hv => AddSubgroup.subset_closure ⟨u, hu, v, hv, rfl⟩
  -- transfers
  have tr : ∀ a b : Fin k, a ≠ b → (Pi.single a (1 : ℤ) - Pi.single b 1) ∈ H := by
    intro a b hab
    have hc : l - 1 ≤ ((Finset.univ : Finset (Fin k)) \ {a, b}).card := by
      have : ((Finset.univ : Finset (Fin k)) \ {a, b}).card + ({a, b} : Finset (Fin k)).card = k := by
        rw [Finset.card_sdiff_add_card_eq_card (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin]
      rw [Finset.card_pair hab] at this
      omega
    obtain ⟨R, hRs, hR⟩ := Finset.exists_subset_card_eq hc
    have haR : a ∉ R := fun h => by simpa using hRs h
    have hbR : b ∉ R := fun h => by simpa using hRs h
    have hu : (fun c => decide (c ∈ insert b R)) ∈ Ham k S := by
      show hw _ ∈ S
      rw [hw_decide_mem, Finset.card_insert_of_notMem hbR, hR, Nat.sub_add_cancel hl1]; exact hl
    have hv : (fun c => decide (c ∈ insert a R)) ∈ Ham k S := by
      show hw _ ∈ S
      rw [hw_decide_mem, Finset.card_insert_of_notMem haR, hR, Nat.sub_add_cancel hl1]; exact hl
    convert gen _ hu _ hv using 1
    funext c
    by_cases hca : c = a
    · subst hca; simp [hab, haR]
    · by_cases hcb : c = b
      · subst hcb; simp [hbR, Ne.symm hab]
      · simp [hca, hcb]
  -- sum-zero vectors
  have k0 : 0 < k := by omega
  let c0 : Fin k := ⟨0, k0⟩
  have sz : ∀ w : Fin k → ℤ, ∑ c, w c = 0 → w ∈ H := by
    intro w hw0
    have hrep : w = ∑ c, w c • (Pi.single c (1 : ℤ) - Pi.single c0 1) := by
      funext j
      simp only [Finset.sum_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, mul_sub,
        Finset.sum_sub_distrib, Pi.single_apply, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq, Finset.mem_univ, if_true]
      by_cases hj : j = c0
      · subst hj; simp [hw0]
      · simp [hj]
    rw [hrep]
    refine AddSubgroup.sum_mem _ (fun c _ => AddSubgroup.zsmul_mem _ ?_ _)
    by_cases hc : c = c0
    · subst hc; simp
    · exact tr c c0 hc
  obtain ⟨x1, hx1⟩ := exists_hw_eq (k := k) (w := l) (by omega)
  obtain ⟨x2, hx2⟩ := exists_hw_eq (k := k) (w := l') hl'k
  have hd := gen x1 (by show hw x1 ∈ S; rw [hx1]; exact hl) x2
    (by show hw x2 ∈ S; rw [hx2]; exact hl')
  obtain ⟨j, hj⟩ := hz
  have hsum : ∑ c, ((fun c => (if x2 c then (1 : ℤ) else 0) - (if x1 c then 1 else 0)) c) =
      (l' : ℤ) - l := by
    simp only [Finset.sum_sub_distrib, sum_boole_hw, hx1, hx2]
  have : z - j • (fun c => (if x2 c then (1 : ℤ) else 0) - (if x1 c then 1 else 0)) ∈ H := by
    apply sz
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_sub_distrib,
      ← Finset.mul_sum, sum_boole_hw, hx1, hx2]
    rw [hj]; ring
  have h2 := H.add_mem this (H.zsmul_mem hd j)
  simpa using h2

theorem exists_int_sign_sum {k : ℕ} (y : Fin k → Bool) (T : ℤ)
    (h : ((∃ c, y c = true) ∧ (hw y : ℤ) ≤ T) ∨ ((∃ c, y c = false) ∧ T ≤ hw y)) :
    ∃ t : Fin k → ℤ, ∑ c, t c = T ∧ ∀ c, decide (0 < t c) = y c := by
  have key : ∀ c0 : Fin k, (y c0 = true → (hw y : ℤ) ≤ T) → (y c0 = false → T ≤ hw y) →
      ∃ t : Fin k → ℤ, ∑ c, t c = T ∧ ∀ c, decide (0 < t c) = y c := by
    intro c0 h1 h2
    refine ⟨fun c => (if y c then 1 else 0) + if c = c0 then T - hw y else 0, ?_, ?_⟩
    · rw [Finset.sum_add_distrib, sum_boole_hw]; simp
    · intro c
      by_cases hc : c = c0
      · subst hc; cases hy : y c <;> simp [hy] at h1 h2 ⊢ <;> omega
      · cases hy : y c <;> simp [hy, hc]
  rcases h with ⟨⟨c0, hc0⟩, hT⟩ | ⟨⟨c0, hc0⟩, hT⟩
  · exact key c0 (fun _ => hT) (fun h' => by rw [hc0] at h'; cases h')
  · exact key c0 (fun h' => by rw [hc0] at h'; cases h') (fun _ => hT)

end Aux_mem_ATImage_ham_of_sign_sum

open Aux_mem_ATImage_ham_of_sign_sum in
/-- `AT(Ham_k(S))` contains every `y ∈ {0,1}^k` that is the positivity pattern of an integer vector with total `T`, whenever `T ≡ ℓ (mod ℓ' - ℓ)` for some `ℓ, ℓ' ∈ S` with `1 ≤ ℓ ≤ k - 1`, `ℓ' ≤ k`; the condition on `(y, T)` is exactly that such an integer vector exists. -/
theorem mem_ATImage_ham_of_sign_sum {k : ℕ} {S : Set ℕ} {l l' : ℕ} (hl : l ∈ S) (hl1 : 1 ≤ l)
    (hlk : l + 1 ≤ k) (hl' : l' ∈ S) (hl'k : l' ≤ k) (y : Fin k → Bool) (T : ℤ)
    (hT : ((l' : ℤ) - l) ∣ T - l)
    (h : ((∃ c, y c = true) ∧ (hw y : ℤ) ≤ T) ∨ ((∃ c, y c = false) ∧ T ≤ hw y)) :
    y ∈ ATImage (Ham k S) := by
  obtain ⟨x, hx⟩ := exists_hw_eq (k := k) (w := l) (by omega)
  obtain ⟨t, ht, hty⟩ := exists_int_sign_sum y T h
  have hz := ham_diffClosure hl hl1 hlk hl' hl'k (t - fun c => if x c then 1 else 0)
    (by simp only [Pi.sub_apply, Finset.sum_sub_distrib, sum_boole_hw, hx, ht]; exact hT)
  have hm := mem_ATImage_of_mem_diffClosure (Ham k S) (x := x)
    (show hw x ∈ S by rw [hx]; exact hl) hz
  convert hm using 1
  funext c
  rw [← hty c]; simp

end SymBoolPCSP.CFixing

open SymBoolPCSP.CFixing in
theorem solution {k : ℕ} {S : Set ℕ} {l l' : ℕ} (hl : l ∈ S) (hl1 : 1 ≤ l)
    (hlk : l + 1 ≤ k) (hl' : l' ∈ S) (hl'k : l' ≤ k) (y : Fin k → Bool) (T : ℤ)
    (hT : ((l' : ℤ) - l) ∣ T - l)
    (h : ((∃ c, y c = true) ∧ (hw y : ℤ) ≤ T) ∨ ((∃ c, y c = false) ∧ T ≤ hw y)) :
    y ∈ ATImage (Ham k S) :=
  SymBoolPCSP.CFixing.mem_ATImage_ham_of_sign_sum hl hl1 hlk hl' hl'k y T hT h
