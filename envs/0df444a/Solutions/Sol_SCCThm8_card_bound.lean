-- Prove2me | solution 1 for SCCThm8.card_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:58:28.110945+00:00
-- url     : https://prove2.me/submissions/9b43c260-b1cf-4b86-8f16-b4f9f28a4efa

module
public import Definitions.Def_SCCThm8_Defs
public import Definitions.Def_SCCThm8_Counting
public import Theorems.Thm_SCCThm8_psi_add
public import Theorems.Thm_SCCThm8_sum_cntLift
public import Theorems.Thm_SCCThm8_cntLift_bounds
public import Theorems.Thm_SCCThm8_mem_iff_cntLift_ne
public import Theorems.Thm_SCCThm8_cntLift_diff

set_option autoImplicit true
@[expose] public section
public section
open SCCThm8
open Finset
namespace SCCThm8
theorem _root_.solution {G : Type*} [Group G] [Fintype G] {n : ℕ} (hn : 1 ≤ n) (g : Fin n → G)
    (hc : ∀ i j, Commute (g i) (g j))
    (hE : ∀ e : Fin n → ℤ, (∀ i, -1 ≤ e i ∧ e i ≤ 2) → ∑ i, e i = 0 → e ≠ 0 → psi g e ≠ 1) :
    2 ^ (n - 1) ≤ Fintype.card G := by
  -- one-sided injectivity step
  have aux : ∀ v v' : Finset (Fin n), Even v.card → Even v'.card →
      psi g (cntLift v) = psi g (cntLift v') → (∀ i, -1 ≤ cntLift v i - cntLift v' i) →
      v = v' := by
    intro v v' hv hv' hpsi hd
    by_contra hne
    obtain ⟨d, hd_def⟩ : ∃ d : Fin n → ℤ, d = fun i => cntLift v i - cntLift v' i := ⟨_, rfl⟩
    have hsplit : psi g (cntLift v) = psi g d * psi g (cntLift v') := by
      rw [← psi_add g hc]
      congr 1
      funext i
      simp [hd_def]
    rw [hsplit] at hpsi
    have hd1 : psi g d = 1 := by
      have := hpsi.trans (one_mul (psi g (cntLift v'))).symm
      exact mul_right_cancel this
    refine hE d (fun i => ?_) ?_ ?_ hd1
    · have := cntLift_bounds v i
      have := cntLift_bounds v' i
      have := hd i
      subst hd_def
      show -1 ≤ cntLift v i - cntLift v' i ∧ cntLift v i - cntLift v' i ≤ 2
      constructor <;> omega
    · subst hd_def
      rw [sum_sub_distrib, sum_cntLift v hv, sum_cntLift v' hv', sub_zero]
    · intro h0
      apply hne
      ext i
      have := congrFun h0 i
      subst hd_def
      simp only [Pi.zero_apply] at this
      rw [mem_iff_cntLift_ne, mem_iff_cntLift_ne]
      omega
  have key : ∀ v v' : Finset (Fin n), Even v.card → Even v'.card →
      psi g (cntLift v) = psi g (cntLift v') → v = v' := by
    intro v v' hv hv' hpsi
    rcases cntLift_diff v v' with h | h
    · exact aux v v' hv hv' hpsi h
    · exact (aux v' v hv' hv hpsi.symm h).symm
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  let φ : Finset (Fin m) → Finset (Fin (m + 1)) := fun w =>
    if Even w.card then w.map Fin.castSuccEmb
    else insert (Fin.last m) (w.map Fin.castSuccEmb)
  have hφmem : ∀ w (i : Fin m), Fin.castSucc i ∈ φ w ↔ i ∈ w := by
    intro w i
    simp only [φ]
    split_ifs <;> simp [Fin.castSucc_ne_last]
  have hφinj : Function.Injective φ := fun w w' h => by
    ext i
    rw [← hφmem, h, hφmem]
  have hφeven : ∀ w, Even (φ w).card := by
    intro w
    simp only [φ]
    split_ifs with h
    · simpa using h
    · rw [card_insert_of_notMem (by simp [Fin.castSucc_ne_last]), card_map]
      exact (Nat.not_even_iff_odd.1 h).add_one
  have hinj : Function.Injective (fun w => psi g (cntLift (φ w))) := fun w w' h =>
    hφinj (key _ _ (hφeven w) (hφeven w') h)
  have := Fintype.card_le_of_injective _ hinj
  simpa [Fintype.card_finset] using this
end SCCThm8
