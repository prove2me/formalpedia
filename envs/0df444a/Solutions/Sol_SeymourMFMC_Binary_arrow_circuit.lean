-- Prove2me | solution 1 for SeymourMFMC.Binary.arrow_circuit
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-28T09:13:08.821528+00:00
-- url     : https://prove2.me/submissions/a348c2b6-e221-4fbd-8380-91818300d2d7

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sym
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Sym.Sym2
import Mathlib.Data.List.Chain
import Mathlib.Data.List.Perm.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Ring.Parity
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Linarith
import Definitions.Def_SeymourMFMC_Binary_blocker
import Definitions.Def_SeymourMFMC_Binary_IsClutter
import Definitions.Def_SeymourMFMC_Binary_IsBinary
import Definitions.Def_SeymourMFMC_Binary_IsMengerian
import Definitions.Def_SeymourMFMC_Binary_IsCritical
import Definitions.Def_SeymourMFMC_Binary_IsCircuit
import Definitions.Def_SeymourMFMC_Binary_tau
import Definitions.Def_SeymourMFMC_Binary_Arrow
import Theorems.Thm_SeymourMFMC_Binary_circuit_card_ge_two
import Theorems.Thm_SeymourMFMC_Binary_parity_decomposition

namespace SeymourMFMC.Binary

private def load {α : Type*} [DecidableEq α] (L : Finset (Finset α))
    (q : Finset α → ℕ) (z : α) : ℕ :=
  ∑ A ∈ L.filter (fun A => z ∈ A), q A

private def w₂ {α : Type*} [DecidableEq α] (x y z : α) : ℕ :=
  if z = x then 0 else if z = y then 2 else 1

private lemma sum_load_eq {α : Type*} [DecidableEq α] (L : Finset (Finset α))
    (q : Finset α → ℕ) (B : Finset α) :
    ∑ z ∈ B, load L q z = ∑ A ∈ L, q A * (A ∩ B).card := by
  unfold load
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun A _ => ?_
  rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_comm]
  congr 2
  ext z
  simp only [Finset.mem_filter, Finset.mem_inter, and_comm]

private lemma sum_le_sum_load {α : Type*} [DecidableEq α] (L : Finset (Finset α))
    (q : Finset α → ℕ) {B : Finset α} (hB : B ∈ blocker L) :
    ∑ A ∈ L, q A ≤ ∑ z ∈ B, load L q z := by
  rw [sum_load_eq]
  rw [blocker, Finset.mem_filter] at hB
  refine Finset.sum_le_sum fun A hA => ?_
  have hpos : 1 ≤ (A ∩ B).card := Finset.card_pos.mpr (hB.2.1 A hA)
  exact Nat.le_mul_of_pos_right _ hpos

private lemma eq_of_le_of_sum_ge {α : Type*} [DecidableEq α] {B : Finset α} {f g : α → ℕ}
    (hle : ∀ z ∈ B, f z ≤ g z) (hsum : ∑ z ∈ B, g z ≤ ∑ z ∈ B, f z)
    {z : α} (hz : z ∈ B) : f z = g z := by
  have h1 := Finset.add_sum_erase B f hz
  have h2 := Finset.add_sum_erase B g hz
  have h3 : ∑ u ∈ B.erase z, f u ≤ ∑ u ∈ B.erase z, g u :=
    Finset.sum_le_sum fun u hu => hle u (Finset.mem_of_mem_erase hu)
  have h4 := hle z hz
  omega

private lemma sum_mul_odd_mod_two {α : Type*} [DecidableEq α] (L : Finset (Finset α))
    (g : Finset α → ℕ) (B : Finset α) (hodd : ∀ A ∈ L, Odd (A ∩ B).card) :
    (∑ A ∈ L, g A * (A ∩ B).card) % 2 = (∑ A ∈ L, g A) % 2 := by
  induction L using Finset.induction_on with
  | empty => rfl
  | @insert A s hAs ih =>
    rw [Finset.sum_insert hAs, Finset.sum_insert hAs]
    have hs := ih (fun A' hA' => hodd A' (Finset.mem_insert_of_mem hA'))
    rcases hodd A (Finset.mem_insert_self A s) with ⟨m, hm⟩
    have hmul : g A * (A ∩ B).card = 2 * (g A * m) + g A := by
      rw [hm, Nat.mul_add, Nat.mul_one, ← Nat.mul_assoc, Nat.mul_comm (g A) 2, Nat.mul_assoc]
    omega

private lemma card_filter_odd_mod_two {α : Type*} [DecidableEq α] (B : Finset α) (f : α → ℕ)
    [DecidablePred (fun z => Odd (f z))] :
    (B.filter (fun z => Odd (f z))).card % 2 = (∑ z ∈ B, f z) % 2 := by
  induction B using Finset.induction_on with
  | empty => rfl
  | @insert a s has ih =>
    rw [Finset.sum_insert has, Finset.filter_insert]
    split_ifs with ha
    · rw [Finset.card_insert_of_notMem (by simp [has])]
      rcases ha with ⟨k, hk⟩
      omega
    · rw [Nat.not_odd_iff_even] at ha
      rcases ha with ⟨k, hk⟩
      omega

private lemma tau_le_card_of_mem_blocker {α : Type*} [DecidableEq α] (L : Finset (Finset α))
    {B : Finset α} (hB : B ∈ blocker L) : tau L ≤ B.card := by
  unfold tau
  rw [dif_pos ⟨B, hB⟩]
  exact Finset.min'_le _ _ (Finset.mem_image_of_mem _ hB)

private lemma ne_singleton_empty_of_mem_ground {α : Type*} [DecidableEq α]
    {L : Finset (Finset α)} {x : α} (hx : x ∈ ground L) : L ≠ {∅} := by
  rintro rfl
  rw [ground, Finset.sup_singleton, id_eq] at hx
  exact Finset.notMem_empty x hx

private lemma sum_ite_eq_one {α : Type*} [DecidableEq α] (B : Finset α) (x : α) :
    (∑ z ∈ B, if z = x then 1 else 0) = if x ∈ B then 1 else 0 := by
  induction B using Finset.induction_on with
  | empty => simp
  | @insert a s has ih =>
    rw [Finset.sum_insert has, ih]
    simp only [Finset.mem_insert]
    (repeat split_ifs) <;> simp_all

private lemma sum_ite_notMem {α : Type*} [DecidableEq α] (B S : Finset α) :
    (∑ z ∈ B, if z ∈ S then 0 else 1) = (B \ S).card := by
  induction B using Finset.induction_on with
  | empty => simp
  | @insert a s has ih =>
    rw [Finset.sum_insert has, ih]
    split_ifs with ha
    · have h : insert a s \ S = s \ S := by
        ext z; simp only [Finset.mem_sdiff, Finset.mem_insert]
        constructor
        · rintro ⟨rfl | hzs, hzS⟩
          · exact ( hzS ha ).elim
          · exact ⟨hzs, hzS⟩
        · rintro ⟨hzs, hzS⟩; exact ⟨Or.inr hzs, hzS⟩
      rw [h]
      omega
    · have h : insert a s \ S = insert a (s \ S) := by
        ext z; simp only [Finset.mem_sdiff, Finset.mem_insert]
        constructor
        · rintro ⟨rfl | hzs, hzS⟩
          · exact Or.inl rfl
          · exact Or.inr ⟨hzs, hzS⟩
        · rintro (rfl | ⟨hzs, hzS⟩)
          · exact ⟨Or.inl rfl, ha⟩
          · exact ⟨Or.inr hzs, hzS⟩
      rw [h, Finset.card_insert_of_notMem (by simp [has])]
      omega

private lemma sum_w2_eq {α : Type*} [DecidableEq α] {x y : α} (hxy : x ≠ y) (B : Finset α) :
    (∑ z ∈ B, w₂ x y z) + (if x ∈ B then 1 else 0) = B.card + (if y ∈ B then 1 else 0) := by
  have hpt : ∀ z ∈ B, w₂ x y z + (if z = x then 1 else 0) = 1 + (if z = y then 1 else 0) := by
    intro z _
    unfold w₂
    split_ifs with h1 h2
    · subst h1; exact (hxy h2).elim
    · omega
    · omega
    · omega
  have hsum := Finset.sum_congr rfl hpt
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one,
    sum_ite_eq_one B x, sum_ite_eq_one B y] at hsum
  exact hsum

/-- Seymour 1977, (4.4), p. 207: if `L` is a critical Mengerian binary clutter and `x → y`, then
there is a circuit `C` of `L` such that (i) `x, y ∈ C`, (ii) `|C| ≥ 3`, (iii) `z → y` for every
`z ∈ C − {y}`, and (iv) `|B − (C − {y})| ≥ τ(L) − 1` for every `B ∈ b(L)` (stated additively as
`τ(L) ≤ |B − (C − {y})| + 1`). -/
theorem arrow_circuit {α : Type*} [DecidableEq α] (L : Finset (Finset α))
    (hL : IsClutter L) (hbin : IsBinary L) (hM : IsMengerian L) (hcrit : IsCritical L)
    (x y : α) (hxy : Arrow L x y) :
    ∃ C : Finset α, IsCircuit L C ∧ x ∈ C ∧ y ∈ C ∧ 3 ≤ C.card ∧
      (∀ z ∈ C.erase y, Arrow L z y) ∧
      ∀ B ∈ blocker L, tau L ≤ (B \ C.erase y).card + 1 := by
  classical
  rcases hxy with ⟨hxG, hyG, hxy_mb, hy_not_pt⟩
  have hxy_ne : x ≠ y := fun h => hy_not_pt (h ▸ Finset.mem_insert_self x _)
  have hL_ne : L ≠ {∅} := ne_singleton_empty_of_mem_ground hxG
  have hM_pack := hM.resolve_left hL_ne
  -- Witness B₀ ∈ mb L with x ∈ B₀ (and hence y ∈ B₀)
  have hx_mbG : x ∈ ground (mb L) := hcrit.symm ▸ hxG
  rw [ground, Finset.mem_sup] at hx_mbG
  rcases hx_mbG with ⟨B₀, hB₀_mb, hxB₀⟩
  change x ∈ B₀ at hxB₀
  have hyB₀ : y ∈ B₀ := hxy_mb B₀ hB₀_mb hxB₀
  have hB₀_bl : B₀ ∈ blocker L := (Finset.mem_filter.mp hB₀_mb).1
  have hB₀_card : B₀.card = tau L := (Finset.mem_filter.mp hB₀_mb).2
  -- Packing q₁ for constant weight w₁ = 1
  obtain ⟨q₁, hq₁_le, B₁, hB₁_bl, hq₁_sum, hB₁_min⟩ := hM_pack (fun _ => 1)
  change ∀ z ∈ ground L, load L q₁ z ≤ 1 at hq₁_le
  have hsum_q₁ : ∑ A ∈ L, q₁ A = tau L := by
    have h1 := hB₁_min B₀ hB₀_bl
    have h2 := tau_le_card_of_mem_blocker L hB₁_bl
    simp only [Finset.sum_const, smul_eq_mul, mul_one] at hq₁_sum h1
    omega
  have hload_q₁ : ∀ z ∈ ground L, load L q₁ z = 1 := by
    intro z hz
    have hz_mb : z ∈ ground (mb L) := hcrit.symm ▸ hz
    rw [ground, Finset.mem_sup] at hz_mb
    rcases hz_mb with ⟨B, hB_mb, hzB⟩
    have hB_bl : B ∈ blocker L := (Finset.mem_filter.mp hB_mb).1
    have hB_card : B.card = tau L := (Finset.mem_filter.mp hB_mb).2
    have hBG : B ⊆ ground L := Finset.mem_powerset.mp (Finset.mem_filter.mp hB_bl).1
    have hle : ∀ u ∈ B, load L q₁ u ≤ (fun _ => 1) u := fun u hu => hq₁_le u (hBG hu)
    have hge : ∑ u ∈ B, (1 : ℕ) ≤ ∑ u ∈ B, load L q₁ u := by
      simp only [Finset.sum_const, smul_eq_mul, mul_one, hB_card, ← hsum_q₁]
      exact sum_le_sum_load L q₁ hB_bl
    exact eq_of_le_of_sum_ge hle hge hzB
  -- Packing q₂ for w₂ x y
  have hw₂_ge_tau : ∀ B ∈ blocker L, tau L ≤ ∑ z ∈ B, w₂ x y z := by
    intro B hB
    have hsum := sum_w2_eq hxy_ne B
    have htau := tau_le_card_of_mem_blocker L hB
    by_cases hcard : B.card = tau L
    · have hB_mb : B ∈ mb L := Finset.mem_filter.mpr ⟨hB, hcard⟩
      have hxyB : x ∈ B → y ∈ B := hxy_mb B hB_mb
      by_cases hxB : x ∈ B <;> by_cases hyB : y ∈ B
      · simp only [hxB, hyB, ↓reduceIte] at hsum; omega
      · exact (hyB (hxyB hxB)).elim
      · simp only [hxB, hyB, ↓reduceIte] at hsum; omega
      · simp only [hxB, hyB, ↓reduceIte] at hsum; omega
    · by_cases hxB : x ∈ B <;> by_cases hyB : y ∈ B <;>
        simp only [hxB, hyB, ↓reduceIte] at hsum <;> omega
  have hw₂_B₀ : ∑ z ∈ B₀, w₂ x y z = tau L := by
    have hsum := sum_w2_eq hxy_ne B₀
    rw [if_pos hxB₀, if_pos hyB₀, hB₀_card] at hsum
    omega
  obtain ⟨q₂, hq₂_le, B₂, hB₂_bl, hq₂_sum, hB₂_min⟩ := hM_pack (w₂ x y)
  change ∀ z ∈ ground L, load L q₂ z ≤ w₂ x y z at hq₂_le
  have hsum_q₂ : ∑ A ∈ L, q₂ A = tau L := by
    have h1 := hB₂_min B₀ hB₀_bl
    have h2 := hw₂_ge_tau B₂ hB₂_bl
    omega
  have hB₀G : B₀ ⊆ ground L := Finset.mem_powerset.mp (Finset.mem_filter.mp hB₀_bl).1
  have hB₀_tight : ∀ z ∈ B₀, load L q₂ z = w₂ x y z := by
    intro z hz
    refine eq_of_le_of_sum_ge (fun u hu => hq₂_le u (hB₀G hu)) ?_ hz
    rw [hw₂_B₀, ← hsum_q₂]
    exact sum_le_sum_load L q₂ hB₀_bl
  have hload_q₂_x : load L q₂ x = 0 := by
    have h := hB₀_tight x hxB₀
    unfold w₂ at h
    rw [if_pos rfl] at h
    exact h
  -- Cycle Z = {z ∈ ground L | Even (load L q₂ z)}
  let Z : Finset α := (ground L).filter (fun z => Even (load L q₂ z))
  have hZG : Z ⊆ ground L := Finset.filter_subset _ _
  have hxZ : x ∈ Z := Finset.mem_filter.mpr ⟨hxG, hload_q₂_x ▸ Even.zero⟩
  have hZ_even : ∀ B ∈ blocker L, Even (Z ∩ B).card := by
    intro B hB
    have hBG : B ⊆ ground L := Finset.mem_powerset.mp (Finset.mem_filter.mp hB).1
    have heq : Z ∩ B = B.filter (fun z => Odd (load L q₁ z + load L q₂ z)) := by
      ext z
      simp only [Z, Finset.mem_inter, Finset.mem_filter]
      constructor
      · rintro ⟨⟨hzG, hev⟩, hzB⟩
        refine ⟨hzB, ?_⟩
        rw [hload_q₁ z hzG]
        rcases hev with ⟨k, hk⟩
        exact ⟨k, by omega⟩
      · rintro ⟨hzB, hodd⟩
        have hzG := hBG hzB
        refine ⟨⟨hzG, ?_⟩, hzB⟩
        rw [hload_q₁ z hzG] at hodd
        rcases hodd with ⟨k, hk⟩
        exact ⟨k, by omega⟩
    rw [heq, Nat.even_iff, card_filter_odd_mod_two, Finset.sum_add_distrib,
      sum_load_eq L q₁ B, sum_load_eq L q₂ B]
    have h1 := sum_mul_odd_mod_two L q₁ B (fun A hA => hbin A hA B hB)
    have h2 := sum_mul_odd_mod_two L q₂ B (fun A hA => hbin A hA B hB)
    rw [hsum_q₁] at h1
    rw [hsum_q₂] at h2
    omega
  obtain ⟨Cs, hCs_circ, _, hCs_sup⟩ := (parity_decomposition L hL hbin Z hZG).1 hZ_even
  have hx_sup : x ∈ Cs.sup id := hCs_sup.symm ▸ hxZ
  rw [Finset.mem_sup] at hx_sup
  rcases hx_sup with ⟨C, hCCs, hxC⟩
  have hC_circ : IsCircuit L C := hCs_circ C hCCs
  have hCZ : C ⊆ Z := hCs_sup ▸ Finset.le_sup (f := id) hCCs
  have hC_er_zero : ∀ z ∈ C.erase y, load L q₂ z = 0 := by
    intro z hz
    have hzy : z ≠ y := (Finset.mem_erase.mp hz).1
    have hzZ : z ∈ Z := hCZ (Finset.mem_erase.mp hz).2
    rw [Finset.mem_filter] at hzZ
    have hle : load L q₂ z ≤ 1 := by
      have h := hq₂_le z hzZ.1
      unfold w₂ at h
      split_ifs at h <;> omega
    rcases hzZ.2 with ⟨k, hk⟩
    omega
  -- Property (iv): ∀ B ∈ blocker L, tau L ≤ (B \ C.erase y).card + 1
  have hC_tau : ∀ B ∈ blocker L, tau L ≤ (B \ C.erase y).card + 1 := by
    intro B hB
    have hBG : B ⊆ ground L := Finset.mem_powerset.mp (Finset.mem_filter.mp hB).1
    have hpt : ∀ z ∈ B,
        load L q₂ z ≤ (if z ∈ C.erase y then 0 else 1) + (if z = y then 1 else 0) := by
      intro z hzB
      by_cases hzy : z = y
      · subst hzy
        rw [if_neg (Finset.notMem_erase z C), if_pos rfl]
        have h := hq₂_le z (hBG hzB)
        unfold w₂ at h
        split_ifs at h <;> omega
      · by_cases hzC : z ∈ C.erase y
        · rw [if_pos hzC, if_neg hzy, hC_er_zero z hzC]
        · rw [if_neg hzC, if_neg hzy]
          have h := hq₂_le z (hBG hzB)
          unfold w₂ at h
          split_ifs at h <;> omega
    have hsum_le := Finset.sum_le_sum hpt
    have hsum1 := sum_ite_notMem B (C.erase y)
    have hsum2 : ∑ z ∈ B, (if z = y then 1 else 0) ≤ 1 := by
      rw [sum_ite_eq_one B y]
      split_ifs <;> omega
    rw [Finset.sum_add_distrib, hsum1] at hsum_le
    have hge := sum_le_sum_load L q₂ hB
    rw [hsum_q₂] at hge
    omega
  -- Property (i): y ∈ C
  have hyC : y ∈ C := by
    by_contra hy_not_C
    have hC_er_eq : C.erase y = C := Finset.erase_eq_of_notMem hy_not_C
    have htau0 := hC_tau B₀ hB₀_bl
    have hsum0 := Finset.card_sdiff_add_card_inter B₀ C
    rw [hC_er_eq] at htau0
    have hle1 : (B₀ ∩ C).card ≤ 1 := by omega
    have hx_inter : x ∈ C ∩ B₀ := Finset.mem_inter.mpr ⟨hxC, hxB₀⟩
    have hpos : 1 ≤ (C ∩ B₀).card := Finset.card_pos.mpr ⟨x, hx_inter⟩
    rw [Finset.inter_comm] at hle1
    rcases hC_circ.2.1.2 B₀ hB₀_bl with ⟨k, hk⟩
    omega
  -- Property (ii): 3 ≤ C.card
  have hcard3 : 3 ≤ C.card := by
    have hge2 : 2 ≤ C.card := circuit_card_ge_two L hL hbin C hC_circ
    by_contra hlt3
    have hcard2 : C.card = 2 := by omega
    have hC_eq : C = {x, y} := by
      have hsub : {x, y} ⊆ C := by
        intro z hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl <;> assumption
      exact (Finset.eq_of_subset_of_card_le hsub (by rw [hcard2, Finset.card_pair hxy_ne])).symm
    apply hy_not_pt
    rw [point, Finset.mem_insert, Finset.mem_filter]
    exact Or.inr ⟨hyG, hC_eq ▸ hC_circ⟩
  -- Property (iii): ∀ z ∈ C.erase y, Arrow L z y
  have hC_arr : ∀ z ∈ C.erase y, Arrow L z y := by
    intro z hz
    have hzy_ne : z ≠ y := (Finset.mem_erase.mp hz).1
    have hzC : z ∈ C := (Finset.mem_erase.mp hz).2
    have hzG : z ∈ ground L := hC_circ.2.1.1 hzC
    refine ⟨hzG, hyG, ?_, ?_⟩
    · intro B hB_mb hzB
      by_contra hy_not_B
      have hB_bl : B ∈ blocker L := (Finset.mem_filter.mp hB_mb).1
      have hB_card : B.card = tau L := (Finset.mem_filter.mp hB_mb).2
      have hBG : B ⊆ ground L := Finset.mem_powerset.mp (Finset.mem_filter.mp hB_bl).1
      have hx_not_B : x ∉ B := fun hxB => hy_not_B (hxy_mb B hB_mb hxB)
      have hw₂_B : ∀ u ∈ B, w₂ x y u = 1 := by
        intro u huB
        have hux : u ≠ x := fun h => hx_not_B (h ▸ huB)
        have huy : u ≠ y := fun h => hy_not_B (h ▸ huB)
        unfold w₂
        rw [if_neg hux, if_neg huy]
      have hsum_w₂_B : ∑ u ∈ B, w₂ x y u = tau L := by
        rw [Finset.sum_congr rfl hw₂_B, Finset.sum_const, smul_eq_mul, mul_one, hB_card]
      have htight_z : load L q₂ z = w₂ x y z := by
        refine eq_of_le_of_sum_ge (fun u hu => hq₂_le u (hBG hu)) ?_ hzB
        rw [hsum_w₂_B, ← hsum_q₂]
        exact sum_le_sum_load L q₂ hB_bl
      rw [hC_er_zero z hz, hw₂_B z hzB] at htight_z
      omega
    · intro hy_pt_z
      rw [point, Finset.mem_insert, Finset.mem_filter] at hy_pt_z
      rcases hy_pt_z with h | ⟨_, hzy_circ⟩
      · exact hzy_ne h.symm
      · have hss : ({z, y} : Finset α) ∈ C.ssubsets := by
          rw [Finset.mem_ssubsets]
          refine ⟨?_, ?_⟩
          · intro u hu
            simp only [Finset.mem_insert, Finset.mem_singleton] at hu
            rcases hu with rfl | rfl <;> assumption
          · intro hsub
            have hle := Finset.card_le_card hsub
            rw [Finset.card_pair hzy_ne] at hle
            omega
        exact hC_circ.2.2 {z, y} hss (Finset.insert_nonempty z {y}) hzy_circ.2.1
  exact ⟨C, hC_circ, hxC, hyC, hcard3, hC_arr, hC_tau⟩

end SeymourMFMC.Binary

theorem solution {α : Type*} [DecidableEq α] (L : Finset (Finset α))
    (hL : SeymourMFMC.Binary.IsClutter L) (hbin : SeymourMFMC.Binary.IsBinary L)
    (hM : SeymourMFMC.Binary.IsMengerian L) (hcrit : SeymourMFMC.Binary.IsCritical L)
    (x y : α) (hxy : SeymourMFMC.Binary.Arrow L x y) :
    ∃ C : Finset α, SeymourMFMC.Binary.IsCircuit L C ∧ x ∈ C ∧ y ∈ C ∧ 3 ≤ C.card ∧
      (∀ z ∈ C.erase y, SeymourMFMC.Binary.Arrow L z y) ∧
      ∀ B ∈ SeymourMFMC.Binary.blocker L, SeymourMFMC.Binary.tau L ≤ (B \ C.erase y).card + 1 :=
  SeymourMFMC.Binary.arrow_circuit L hL hbin hM hcrit x y hxy
