-- Prove2me | solution 1 for SparseNLO.IHT.lemma_2_2
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T05:31:50.354763+00:00
-- url     : https://prove2.me/submissions/834bdb37-89f0-4b2a-a4a9-f549cb4f10b3

import Mathlib
import Definitions.Def_SparseNLO_IHT_Setting

set_option autoImplicit false
open Filter Topology
open SparseNLO.IHT SparseNLO.CWOpt

theorem sn_Ms_eq {n s : ℕ} (hs : 0 < s) (hsn : s < n) (x : EuclideanSpace ℝ (Fin n))
    (hk : l0 x = s) (m : Fin n) (hm : m ∈ I1 x) (hmin : ∀ i ∈ I1 x, |x m| ≤ |x i|) :
    Ms s x = |x m| := by
  set M : Multiset ℝ := Finset.univ.val.map (fun i => |x i|) with hM
  set L : List ℝ := M.sort (fun a b : ℝ => b ≤ a) with hL
  have hperm : (L : Multiset ℝ) = M := Multiset.sort_eq _ _
  have hlen : L.length = n := by
    rw [hL, Multiset.length_sort]
    simp [hM]
  have hpw : L.Pairwise (fun a b : ℝ => b ≤ a) := Multiset.pairwise_sort _ _
  have hp : s - 1 < L.length := by omega
  have hMs : Ms s x = L[s - 1] := by
    unfold Ms
    rw [List.getD_eq_getElem _ _ hp]
  rw [hMs]
  have hcount : ∀ a : ℝ, L.countP (fun y => decide (a ≤ y)) = (Finset.univ.filter (fun i => a ≤ |x i|)).card := by
    intro a
    have h1 : (↑L : Multiset ℝ).countP (fun y => a ≤ y) = L.countP (fun y => decide (a ≤ y)) := by
      simp
    rw [← h1, hperm, hM, Multiset.countP_map]
    rfl
  have hI1card : (I1 x).card = s := hk
  have hxm : 0 < |x m| := by
    have : x m ≠ 0 := by simpa [I1] using hm
    positivity
  apply le_antisymm
  · by_contra hlt
    push Not at hlt
    -- hlt : |x m| < L[s-1]
    have hA : s ≤ L.countP (fun y => decide (L[s - 1] ≤ y)) := by
      have h1 : ((L.take s).countP (fun y => decide (L[s - 1] ≤ y))) = s := by
        rw [List.countP_eq_length.mpr]
        · simp; omega
        · intro y hy
          obtain ⟨q, hq, rfl⟩ := List.mem_iff_getElem.mp hy
          simp only [List.getElem_take, decide_eq_true_eq]
          have hq' : q < s := by simp at hq; omega
          by_cases hqe : q = s - 1
          · subst hqe; exact le_rfl
          · have := List.pairwise_iff_getElem.mp hpw q (s - 1) (by omega) hp (by omega)
            simpa using this
      exact h1.symm.trans_le (List.take_sublist _ _).countP_le
    rw [hcount] at hA
    have hsub : Finset.univ.filter (fun i => L[s - 1] ≤ |x i|) ⊆ (I1 x).erase m := by
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      simp only [Finset.mem_erase, I1, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨?_, ?_⟩
      · rintro rfl; linarith
      · intro h0; rw [h0] at hi; simp at hi; linarith
    have := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem hm, hI1card] at this
    omega
  · by_contra hlt
    push Not at hlt
    -- hlt : L[s-1] < |x m|
    have hB : L.countP (fun y => decide (|x m| ≤ y)) ≤ s - 1 := by
      rw [← List.take_append_drop (s - 1) L, List.countP_append]
      have h1 : ((L.drop (s - 1)).countP (fun y => decide (|x m| ≤ y))) = 0 := by
        rw [List.countP_eq_zero]
        intro y hy
        obtain ⟨q, hq, rfl⟩ := List.mem_iff_getElem.mp hy
        simp only [List.getElem_drop, decide_eq_true_eq, not_le]
        by_cases hq0 : q = 0
        · subst hq0; simpa using hlt
        · have := List.pairwise_iff_getElem.mp hpw (s - 1) (s - 1 + q) hp (by simp at hq; omega) (by omega)
          exact lt_of_le_of_lt this hlt
      have h2 : ((L.take (s - 1)).countP (fun y => decide (|x m| ≤ y))) ≤ s - 1 := by
        refine List.countP_le_length.trans ?_
        simp
      omega
    rw [hcount] at hB
    have hsub : I1 x ⊆ Finset.univ.filter (fun i => |x m| ≤ |x i|) := by
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hmin i hi
    have := Finset.card_le_card hsub
    rw [hI1card] at this
    omega

theorem sn_Ms_zero {n s : ℕ} (hs : 0 < s) (hsn : s < n) (x : EuclideanSpace ℝ (Fin n))
    (hk : l0 x < s) : Ms s x = 0 := by
  set M : Multiset ℝ := Finset.univ.val.map (fun i => |x i|) with hM
  set L : List ℝ := M.sort (fun a b : ℝ => b ≤ a) with hL
  have hperm : (L : Multiset ℝ) = M := Multiset.sort_eq _ _
  have hlen : L.length = n := by
    rw [hL, Multiset.length_sort]
    simp [hM]
  have hpw : L.Pairwise (fun a b : ℝ => b ≤ a) := Multiset.pairwise_sort _ _
  have hp : s - 1 < L.length := by omega
  have hMs : Ms s x = L[s - 1] := by
    unfold Ms
    rw [List.getD_eq_getElem _ _ hp]
  rw [hMs]
  have hcount : ∀ a : ℝ, L.countP (fun y => decide (a ≤ y)) = (Finset.univ.filter (fun i => a ≤ |x i|)).card := by
    intro a
    have h1 : (↑L : Multiset ℝ).countP (fun y => a ≤ y) = L.countP (fun y => decide (a ≤ y)) := by
      simp
    rw [← h1, hperm, hM, Multiset.countP_map]
    rfl
  have hnn : 0 ≤ L[s - 1] := by
    have hmem : L[s - 1] ∈ (L : Multiset ℝ) := by simp [List.getElem_mem]
    rw [hperm, hM] at hmem
    obtain ⟨i, -, hi⟩ := Multiset.mem_map.mp hmem
    rw [← hi]; exact abs_nonneg _
  refine le_antisymm ?_ hnn
  by_contra hlt
  push Not at hlt
  have hA : s ≤ L.countP (fun y => decide (L[s - 1] ≤ y)) := by
    have h1 : ((L.take s).countP (fun y => decide (L[s - 1] ≤ y))) = s := by
      rw [List.countP_eq_length.mpr]
      · simp; omega
      · intro y hy
        obtain ⟨q, hq, rfl⟩ := List.mem_iff_getElem.mp hy
        simp only [List.getElem_take, decide_eq_true_eq]
        have hq' : q < s := by simp at hq; omega
        by_cases hqe : q = s - 1
        · subst hqe; exact le_rfl
        · have := List.pairwise_iff_getElem.mp hpw q (s - 1) (by omega) hp (by omega)
          simpa using this
    exact h1.symm.trans_le (List.take_sublist _ _).countP_le
  rw [hcount] at hA
  have hsub : Finset.univ.filter (fun i => L[s - 1] ≤ |x i|) ⊆ I1 x := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    simp only [I1, Finset.mem_filter, Finset.mem_univ, true_and]
    intro h0; rw [h0] at hi; simp at hi; linarith
  have := Finset.card_le_card hsub
  have h3 : (I1 x).card = l0 x := rfl
  omega
theorem sih_coord {n s : ℕ} (x y : EuclideanSpace ℝ (Fin n)) (hx : x ∈ projCs n s y) (i : Fin n)
    (hi : l0 x < s ∨ x i ≠ 0) : x i = y i := by
  set z : EuclideanSpace ℝ (Fin n) := x + EuclideanSpace.single i (y i - x i) with hz
  have hzj : ∀ j, z j = if j = i then y i else x j := by
    intro j
    by_cases h : j = i
    · subst h; simp [hz]
    · simp [hz, h, EuclideanSpace.single_apply]
  have hzC : z ∈ Cs n s := by
    have hsub : I1 z ⊆ insert i (I1 x) := by
      intro j hj
      simp only [I1, Finset.mem_filter, Finset.mem_univ, true_and] at hj
      rw [hzj] at hj
      by_cases h : j = i
      · simp [h]
      · simp only [h, if_false] at hj
        simp [I1, hj]
    have hcard := Finset.card_le_card hsub
    show l0 z ≤ s
    have h1 : l0 z = (I1 z).card := rfl
    have h2 : l0 x = (I1 x).card := rfl
    rcases hi with hi | hi
    · have := Finset.card_insert_le i (I1 x)
      omega
    · have hmem : i ∈ I1 x := by simp [I1, hi]
      rw [Finset.insert_eq_of_mem hmem] at hcard
      have := hx.1
      have h3 : l0 x ≤ s := this
      omega
  have hle := hx.2 z hzC
  have hsq : ∀ w : EuclideanSpace ℝ (Fin n), ‖w‖ ^ 2 = ∑ j, (w j) ^ 2 := by
    intro w; rw [EuclideanSpace.norm_sq_eq]; simp
  have h2 : ‖x - y‖ ^ 2 ≤ ‖z - y‖ ^ 2 := by gcongr
  rw [hsq, hsq] at h2
  have hdiff : ∑ j, ((z - y) j) ^ 2 + (x i - y i) ^ 2 = ∑ j, ((x - y) j) ^ 2 := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i), ← Finset.sum_erase_add _ (fun j => ((x - y) j) ^ 2) (Finset.mem_univ i)]
    have : ∑ j ∈ Finset.univ.erase i, ((z - y) j) ^ 2 = ∑ j ∈ Finset.univ.erase i, ((x - y) j) ^ 2 := by
      refine Finset.sum_congr rfl fun j hj => ?_
      have hji : j ≠ i := Finset.ne_of_mem_erase hj
      simp [hzj, hji]
    rw [this]
    have : (z - y) i = 0 := by simp [hzj]
    rw [this]
    simp
  have : (x i - y i) ^ 2 ≤ 0 := by linarith
  have : x i - y i = 0 := by nlinarith [sq_nonneg (x i - y i)]
  linarith


theorem sn_sq {n : ℕ} (w : EuclideanSpace ℝ (Fin n)) : ‖w‖ ^ 2 = ∑ j, (w j) ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]; simp

theorem sn_proj_fwd {n s : ℕ} (hs : 0 < s) (hsn : s < n) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (L : ℝ) (hL : 0 < L) (x : EuclideanSpace ℝ (Fin n))
    (hx : x ∈ projCs n s (x - (1 / L) • gradient f x)) :
    l0 x ≤ s ∧ (∀ i ∈ I0 x, |gradient f x i| ≤ L * Ms s x) ∧ (∀ i ∈ I1 x, gradient f x i = 0) := by
  have hgi : ∀ i, (l0 x < s ∨ x i ≠ 0) → gradient f x i = 0 := by
    intro i hi
    have := sih_coord x _ hx i hi
    have e : (x - (1 / L) • gradient f x) i = x i - (1 / L) * gradient f x i := by simp
    rw [e] at this
    have h2 : (1 / L) * gradient f x i = 0 := by linarith
    rcases mul_eq_zero.mp h2 with h | h
    · exact absurd h (by positivity)
    · exact h
  refine ⟨hx.1, ?_, ?_⟩
  · intro i hi
    have hi0 : x i = 0 := by simpa [I0] using hi
    rcases lt_or_eq_of_le (show l0 x ≤ s from hx.1) with hlt | heq
    · rw [sn_Ms_zero hs hsn x hlt, hgi i (Or.inl hlt)]; simp
    · -- l0 x = s
      have hI1ne : (I1 x).Nonempty := by
        rw [← Finset.card_pos]; show 0 < l0 x; omega
      obtain ⟨m, hm, hmin⟩ := Finset.exists_min_image (I1 x) (fun i => |x i|) hI1ne
      have hMs : Ms s x = |x m| := sn_Ms_eq hs hsn x heq m hm hmin
      have hxm : x m ≠ 0 := by simpa [I1] using hm
      have hne : m ≠ i := by rintro rfl; exact hxm hi0
      set y : EuclideanSpace ℝ (Fin n) := x - (1 / L) • gradient f x with hy
      have hym : y m = x m := by
        have := hgi m (Or.inr hxm)
        simp [hy, this]
      have hyi : y i = -(gradient f x i) / L := by
        simp [hy, hi0]; ring
      set z : EuclideanSpace ℝ (Fin n) := x - EuclideanSpace.single m (x m) + EuclideanSpace.single i (y i) with hz
      have hzj : ∀ j, z j = if j = i then y i else if j = m then 0 else x j := by
        intro j
        by_cases h1 : j = i
        · subst h1; simp [hz, hne.symm, hi0]
        · by_cases h2 : j = m
          · subst h2; simp [hz, h1]
          · simp [hz, h1, h2]
      have hzC : z ∈ Cs n s := by
        have hsub : I1 z ⊆ insert i ((I1 x).erase m) := by
          intro j hj
          simp only [I1, Finset.mem_filter, Finset.mem_univ, true_and] at hj
          rw [hzj] at hj
          by_cases h1 : j = i
          · simp [h1]
          · by_cases h2 : j = m
            · exfalso; apply hj; subst h2; simp [h1]
            · simp only [h1, h2, if_false] at hj
              simp [I1, hj, h1, h2]
        have hcard := Finset.card_le_card hsub
        have := Finset.card_insert_le i ((I1 x).erase m)
        rw [Finset.card_erase_of_mem hm] at this
        have h3 : (I1 x).card = l0 x := rfl
        show l0 z ≤ s
        have h4 : l0 z = (I1 z).card := rfl
        omega
      have hle := hx.2 z hzC
      have h2 : ‖x - y‖ ^ 2 ≤ ‖z - y‖ ^ 2 := by gcongr
      rw [sn_sq, sn_sq] at h2
      have hd : ∑ j, ((x - y) j) ^ 2 - ∑ j, ((z - y) j) ^ 2 = ((x - y) m) ^ 2 + ((x - y) i) ^ 2 - (((z - y) m) ^ 2 + ((z - y) i) ^ 2) := by
        rw [← Finset.sum_sub_distrib, Finset.sum_eq_add m i hne]
        · ring
        · intro j _ hj
          have h1 : j ≠ m := hj.1
          have h2 : j ≠ i := hj.2
          simp [hzj, h1, h2]
        · intro h; exact absurd (Finset.mem_univ _) h
        · intro h; exact absurd (Finset.mem_univ _) h
      have e1 : (x - y) m = 0 := by simp [hym]
      have e2 : (x - y) i = -(y i) := by simp [hi0]
      have e3 : (z - y) m = -(x m) := by simp [hzj, hne, hym]
      have e4 : (z - y) i = 0 := by simp [hzj]
      rw [e1, e2, e3, e4] at hd
      have h5 : (y i) ^ 2 ≤ (x m) ^ 2 := by nlinarith
      rw [hyi, hMs] at *
      have h6 : (gradient f x i) ^ 2 ≤ (L * |x m|) ^ 2 := by
        have : (-(gradient f x i) / L) ^ 2 ≤ (x m) ^ 2 := by rwa [hyi] at h5
        rw [div_pow, div_le_iff₀ (by positivity)] at this
        rw [mul_pow, sq_abs]; nlinarith
      exact abs_le_of_sq_le_sq' h6 (by positivity) |>.2 |> fun h => by
        have := abs_le_of_sq_le_sq' h6 (by positivity)
        exact abs_le.mpr this
  · intro i hi
    exact hgi i (Or.inr (by simpa [I1] using hi))

theorem sn_proj_bwd {n s : ℕ} (hs : 0 < s) (hsn : s < n) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (L : ℝ) (hL : 0 < L) (x : EuclideanSpace ℝ (Fin n))
    (h : l0 x ≤ s ∧ (∀ i ∈ I0 x, |gradient f x i| ≤ L * Ms s x) ∧ (∀ i ∈ I1 x, gradient f x i = 0)) :
    x ∈ projCs n s (x - (1 / L) • gradient f x) := by
  obtain ⟨hl0, hI0, hI1⟩ := h
  refine ⟨hl0, fun z hz => ?_⟩
  set y : EuclideanSpace ℝ (Fin n) := x - (1 / L) • gradient f x with hy
  have hyj : ∀ j, y j = x j - gradient f x j / L := by
    intro j; simp [hy]; ring
  have hy1 : ∀ j ∈ I1 x, y j = x j := by
    intro j hj; rw [hyj, hI1 j hj]; simp
  have hx0 : ∀ j ∈ I0 x, x j = 0 := by intro j hj; simpa [I0] using hj
  have hx1 : ∀ j ∈ I1 x, x j ≠ 0 := by intro j hj; simpa [I1] using hj
  have hy0 : ∀ j ∈ I0 x, |y j| ≤ Ms s x := by
    intro j hj
    rw [hyj, hx0 j hj, zero_sub, abs_neg, abs_div, abs_of_pos hL, div_le_iff₀ hL]
    linarith [hI0 j hj]
  rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), sn_sq, sn_sq]
  set T := I1 z with hT
  have hTcard : T.card ≤ s := hz
  have hzT : ∀ i, i ∉ T → z i = 0 := by
    intro i hi; by_contra h0; exact hi (by simp [hT, I1, h0])
  have hsa : ∑ j, ((x - y) j) ^ 2 = ∑ j ∈ I0 x, (y j) ^ 2 := by
    rw [I0, Finset.sum_filter]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hj : x j = 0
    · simp [hj]
    · have : j ∈ I1 x := by simp [I1, hj]
      simp [hy1 j this, hj]
  set A := (I0 x).filter (fun j => j ∉ T) with hA
  set C := (I0 x).filter (fun j => j ∈ T) with hC
  set Bs := (I1 x).filter (fun j => j ∉ T) with hBs
  set D := (I1 x).filter (fun j => j ∈ T) with hD
  have hsplit : ∑ j ∈ I0 x, (y j) ^ 2 = ∑ j ∈ C, (y j) ^ 2 + ∑ j ∈ A, (y j) ^ 2 :=
    (Finset.sum_filter_add_sum_filter_not (I0 x) (fun j => j ∈ T) (fun j => (y j) ^ 2)).symm
  have hdisj : Disjoint A Bs := by
    rw [Finset.disjoint_left]
    intro j hjA hjB
    have h1 : j ∈ I0 x := (Finset.mem_filter.mp hjA).1
    have h2 : j ∈ I1 x := (Finset.mem_filter.mp hjB).1
    exact hx1 j h2 (hx0 j h1)
  have hb : ∀ j, 0 ≤ ((z - y) j) ^ 2 := fun j => sq_nonneg _
  have hsub : ∑ j ∈ A ∪ Bs, ((z - y) j) ^ 2 ≤ ∑ j, ((z - y) j) ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun j _ _ => hb j)
  rw [Finset.sum_union hdisj] at hsub
  have hSA : ∑ j ∈ A, ((z - y) j) ^ 2 = ∑ j ∈ A, (y j) ^ 2 := by
    refine Finset.sum_congr rfl fun j hj => ?_
    have : j ∉ T := (Finset.mem_filter.mp hj).2
    simp [hzT j this]
  have hSB : ∑ j ∈ Bs, ((z - y) j) ^ 2 = ∑ j ∈ Bs, (x j) ^ 2 := by
    refine Finset.sum_congr rfl fun j hj => ?_
    have h1 : j ∉ T := (Finset.mem_filter.mp hj).2
    have h2 : j ∈ I1 x := (Finset.mem_filter.mp hj).1
    simp [hzT j h1, hy1 j h2]
  rw [hsa, hsplit]
  rw [hSA, hSB] at hsub
  have hBnn : 0 ≤ ∑ j ∈ Bs, (x j) ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
  have hCle : ∑ j ∈ C, (y j) ^ 2 ≤ ∑ j ∈ Bs, (x j) ^ 2 := by
    rcases lt_or_eq_of_le hl0 with hlt | heq
    · have hM0 : Ms s x = 0 := sn_Ms_zero hs hsn x hlt
      have : ∑ j ∈ C, (y j) ^ 2 ≤ 0 := by
        refine Finset.sum_nonpos fun j hj => ?_
        have h1 : j ∈ I0 x := (Finset.mem_filter.mp hj).1
        have := hy0 j h1
        rw [hM0] at this
        have : y j = 0 := abs_nonpos_iff.mp this
        simp [this]
      linarith
    · have hI1ne : (I1 x).Nonempty := by
        rw [← Finset.card_pos]; show 0 < l0 x; omega
      obtain ⟨m, hm, hmin⟩ := Finset.exists_min_image (I1 x) (fun i => |x i|) hI1ne
      have hMs : Ms s x = |x m| := sn_Ms_eq hs hsn x heq m hm hmin
      have hcard1 : D.card + Bs.card = s := by
        have : D.card + Bs.card = (I1 x).card := Finset.card_filter_add_card_filter_not (s := I1 x) (fun j => j ∈ T)
        have h3 : (I1 x).card = l0 x := rfl
        omega
      have hcard2 : C.card + D.card ≤ s := by
        have hdis : Disjoint C D := by
          rw [Finset.disjoint_left]
          intro j hjC hjD
          have h1 : j ∈ I0 x := (Finset.mem_filter.mp hjC).1
          have h2 : j ∈ I1 x := (Finset.mem_filter.mp hjD).1
          exact hx1 j h2 (hx0 j h1)
        have hsub2 : C ∪ D ⊆ T := by
          intro j hj
          rcases Finset.mem_union.mp hj with h | h
          · exact (Finset.mem_filter.mp h).2
          · exact (Finset.mem_filter.mp h).2
        have := Finset.card_le_card hsub2
        rw [Finset.card_union_of_disjoint hdis] at this
        omega
      have hCB : C.card ≤ Bs.card := by omega
      calc ∑ j ∈ C, (y j) ^ 2 ≤ ∑ j ∈ C, (Ms s x) ^ 2 := by
            refine Finset.sum_le_sum fun j hj => ?_
            have h1 : j ∈ I0 x := (Finset.mem_filter.mp hj).1
            have := hy0 j h1
            rw [← sq_abs (y j)]
            exact pow_le_pow_left₀ (abs_nonneg _) this 2
        _ = C.card * (Ms s x) ^ 2 := by simp
        _ ≤ Bs.card * (Ms s x) ^ 2 := by gcongr
        _ = ∑ j ∈ Bs, (Ms s x) ^ 2 := by simp
        _ ≤ ∑ j ∈ Bs, (x j) ^ 2 := by
            refine Finset.sum_le_sum fun j hj => ?_
            have h2 : j ∈ I1 x := (Finset.mem_filter.mp hj).1
            rw [hMs, ← sq_abs (x j)]
            exact pow_le_pow_left₀ (abs_nonneg _) (hmin j h2) 2
  linarith

theorem sn_proj_iff {n s : ℕ} (hs : 0 < s) (hsn : s < n) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (L : ℝ) (hL : 0 < L) (x : EuclideanSpace ℝ (Fin n)) :
    x ∈ projCs n s (x - (1 / L) • gradient f x) ↔
      (l0 x ≤ s ∧ (∀ i ∈ I0 x, |gradient f x i| ≤ L * Ms s x) ∧ (∀ i ∈ I1 x, gradient f x i = 0)) :=
  ⟨sn_proj_fwd hs hsn f L hL x, sn_proj_bwd hs hsn f L hL x⟩

theorem solution {n s : ℕ} (hs : 0 < s) (hsn : s < n)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiff ℝ 1 f) (hbdd : ∃ γ : ℝ, ∀ x, γ ≤ f x)
    (L : ℝ) (hL : 0 < L) (x : EuclideanSpace ℝ (Fin n)) :
    x ∈ projCs n s (x - (1 / L) • gradient f x) ↔
      (l0 x ≤ s ∧
        (∀ i ∈ I0 x, |gradient f x i| ≤ L * Ms s x) ∧
        (∀ i ∈ I1 x, gradient f x i = 0)) :=
  sn_proj_iff hs hsn f L hL x
