-- Prove2me | solution 1 for SublinearChoresMMS.Disposal.lemma_3_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T10:44:41.513658+00:00
-- url     : https://prove2.me/submissions/9f9ffac8-2cc9-43e8-97fd-bc408c6f9af6
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_SublinearChoresMMS_Disposal_Packing
import Theorems.Thm_SublinearChoresMMS_Disposal_lemma_a_2
import Theorems.Thm_SublinearChoresMMS_Disposal_lemma_3_1_rearrangement

section
noncomputable section
namespace SublinearChoresMMS.Disposal.Dev.L31.PartU
open SublinearChoresMMS.Disposal
open Finset
/-! ### Generic helpers -/
lemma stageCapacity_nonneg (n j : ℕ) (v : Fin (stageBins n j)) : 0 ≤ stageCapacity n j v := by
  unfold stageCapacity
  split_ifs <;> positivity

lemma exists_of_iSup_eq {ι κ : Type*} [Finite ι] [Nonempty ι] [Finite κ] [Nonempty κ]
    (F : ι → κ → ℝ) (h : (⨆ x, ⨅ j, F x j) = -1) : ∃ x, ∀ j, -1 ≤ F x j := by
  obtain ⟨x, hx⟩ := exists_eq_ciSup_of_finite (f := fun x => ⨅ j, F x j)
  refine ⟨x, fun j => ?_⟩
  have := ciInf_le (Set.finite_range (F x)).bddBelow j
  linarith

lemma mms_partition {n m : ℕ} (hn : 0 < n) (c : Cost n m) (hc : Normalized c) (i : Fin n) :
    ∃ f : Fin m → Fin n, ∀ j : Fin n, ∀ S : Finset (Fin m), (∀ e ∈ S, f e = j) →
      ∑ e ∈ S, c i e ≤ 1 := by
  classical
  have hmu := hc.2.2 i
  unfold mu costShare LittleCharity.MMS.mms at hmu
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨f, hf⟩ := exists_of_iSup_eq _ (neg_eq_iff_eq_neg.mp hmu)
  refine ⟨f, fun j S hS => ?_⟩
  have h1 := hf j
  simp only at h1
  calc ∑ e ∈ S, c i e ≤ ∑ e ∈ Finset.univ.filter (fun g => f g = j), c i e := by
        apply sum_le_sum_of_subset_of_nonneg
        · intro e he; simp [hS e he]
        · intro e _ _; exact (hc.1 i e).le
    _ ≤ 1 := by
        convert (neg_le_neg_iff.mp (by simpa using h1) : _ ≤ (1:ℝ)) using 2

lemma divmod_inj {q R R' k k' : ℕ} (hk : k < q) (hk' : k' < q) (h : R * q + k = R' * q + k') :
    R = R' ∧ k = k' := by
  have hq : 0 < q := by omega
  have h1 : (R * q + k) / q = R := by
    rw [add_comm, Nat.add_mul_div_right _ _ hq, Nat.div_eq_of_lt hk, zero_add]
  have h2 : (R' * q + k') / q = R' := by
    rw [add_comm, Nat.add_mul_div_right _ _ hq, Nat.div_eq_of_lt hk', zero_add]
  have h3 : (R * q + k) % q = k := by
    rw [add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hk]
  have h4 : (R' * q + k') % q = k' := by
    rw [add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hk']
  constructor
  · rw [← h1, ← h2, h]
  · rw [← h3, ← h4, h]

/-- Chore replaced by copy `k` of representative `r` (zero-based `(r-1)q + k`). -/
def chore0 {m q : ℕ} (s : Copies m q 0) : Fin m :=
  ⟨(s.1.1.val - 1) * q + s.2.val, by
    have hk : s.2.val < q := by simpa using s.2.isLt
    have hr := s.1.2
    have hr' := s.1.1.isLt
    have := Nat.mul_le_mul_right q (show s.1.1.val - 1 + 1 ≤ m / q by omega)
    rw [Nat.add_mul, one_mul] at this
    have := Nat.div_mul_le_self m q
    omega⟩

lemma chore0_inj {m q : ℕ} : Function.Injective (chore0 (m := m) (q := q)) := by
  intro s t h
  have hks : s.2.val < q := by simpa using s.2.isLt
  have hkt : t.2.val < q := by simpa using t.2.isLt
  have h' := congrArg Fin.val h
  simp only [chore0] at h'
  obtain ⟨h1, h2⟩ := divmod_inj hks hkt h'
  have hs := s.1.2
  have ht := t.1.2
  exact Prod.ext (Subtype.ext (Fin.ext (by omega))) (Fin.ext h2)

lemma rep_le_chore0 {n m q : ℕ} (c : Cost n m) (hc : Normalized c) (i : Fin n)
    (s : Copies m q 0) : representativeCost c i q s.1.val ≤ c i (chore0 s) := by
  unfold representativeCost
  split_ifs with h
  · apply (hc.2.1 i).antitone
    rw [Fin.le_iff_val_le_val]
    simp only [chore0]
    have hk : s.2.val < q := by simpa using s.2.isLt
    have hr := s.1.2
    have : (s.1.1.val - 1 + 1) * q = (s.1.1.val - 1) * q + q := by rw [Nat.add_mul, one_mul]
    rw [show s.1.1.val - 1 + 1 = s.1.1.val by omega] at this
    omega
  · exact (hc.1 i _).le

lemma n_le_stageBins0 (n : ℕ) : n ≤ stageBins n 0 := by
  have : binCount n (2 ^ 0) = n := by
    unfold binCount; rw [pow_zero, Nat.div_one, Nat.mod_one, if_pos rfl]; rfl
  show n ≤ binCount n (2 ^ 0) + binCount n (2 ^ 0) % 2
  omega

theorem initial_packing {n m q : ℕ} (hn : 0 < n) (hq : 0 < q) (hdiv : q ∣ m)
    (c : Cost n m) (hc : Normalized c) (i : Fin n) :
    ∃ P : CopyPacking n m q 0, CopyFeasible c i P ∧ P.marked = ∅ := by
  classical
  obtain ⟨f, hf⟩ := mms_partition hn c hc i
  let P : CopyPacking n m q 0 :=
    { location := fun s => ⟨(f (chore0 s)).val,
        lt_of_lt_of_le (f (chore0 s)).isLt (n_le_stageBins0 n)⟩
      marked := ∅ }
  have hcap1 : ∀ v : Fin (stageBins n 0), v.val < n → stageCapacity n 0 v = 1 := by
    intro v hv
    unfold stageCapacity
    rw [if_pos (by simpa using hv)]
  refine ⟨P, ⟨fun v => ?_, fun s hs => ?_⟩, rfl⟩
  · unfold copyLoad
    by_cases hv : v.val < n
    · rw [hcap1 v hv]
      let J : Fin n := ⟨v.val, hv⟩
      calc ∑ s, (if P.location s = v ∧ s ∉ P.marked then representativeCost c i q s.1.val else 0)
          ≤ ∑ s, (if f (chore0 s) = J then c i (chore0 s) else 0) := by
            apply sum_le_sum
            intro s _
            by_cases h : P.location s = v
            · have hJ : f (chore0 s) = J := Fin.ext (by
                have := congrArg Fin.val h; simpa [P, J] using this)
              rw [if_pos ⟨h, by simp [P]⟩, if_pos hJ]
              exact rep_le_chore0 c hc i s
            · simp only [h, false_and, if_false]
              split_ifs
              · exact (hc.1 i _).le
              · exact le_rfl
        _ = ∑ e ∈ (univ.filter (fun s => f (chore0 s) = J)).image chore0, c i e := by
            rw [sum_image (fun x _ y _ h => chore0_inj h), sum_filter]
        _ ≤ 1 := by
            apply hf J
            intro e he
            obtain ⟨s, hs, rfl⟩ := mem_image.mp he
            simpa using hs
    · apply le_trans _ (stageCapacity_nonneg n 0 v)
      apply le_of_eq
      apply sum_eq_zero
      intro s _
      rw [if_neg]
      rintro ⟨h, -⟩
      apply hv
      rw [← h]
      exact (f (chore0 s)).isLt
  · rw [hcap1 _ (f (chore0 s)).isLt] at hs
    exact one_ne_zero hs

end SublinearChoresMMS.Disposal.Dev.L31.PartU
end
end

section
noncomputable section
namespace SublinearChoresMMS.Disposal.Dev.L31
open SublinearChoresMMS.Disposal
open Finset
/-! ## Part U: the stages of Appendix A.1.1–A.1.2 -/
alias initial_packing := SublinearChoresMMS.Disposal.Dev.L31.PartU.initial_packing

end SublinearChoresMMS.Disposal.Dev.L31
end
end

section
noncomputable section
namespace SublinearChoresMMS.Disposal.Dev.L31.PartU
open SublinearChoresMMS.Disposal
open Finset
/-! ### Final labels -/
lemma binCount_le_stageBins (n j : ℕ) : binCount n (2 ^ j) ≤ stageBins n j := by
  show binCount n (2 ^ j) ≤ binCount n (2 ^ j) + binCount n (2 ^ j) % 2
  omega

lemma loc_lt_binCount {n j : ℕ} (v : Fin (stageBins n j)) (h : stageCapacity n j v = 0 → False) :
    v.val < binCount n (2 ^ j) := by
  unfold stageCapacity at h
  unfold binCount
  split_ifs at h with h1 h2
  · omega
  · split_ifs with h3
    · exfalso; apply h; rw [h3]; simp
    · omega
  · exact absurd rfl h

lemma binCapacity_eq {n j : ℕ} (v : Fin (stageBins n j)) (w : Fin (binCount n (2 ^ j)))
    (h : v.val = w.val) : binCapacity n (2 ^ j) w = stageCapacity n j v := by
  have hw := w.isLt
  unfold binCount at hw
  unfold binCapacity stageCapacity
  by_cases h1 : w.val < n / 2 ^ j
  · rw [if_pos h1, if_pos (by omega)]
  · rw [if_neg h1, if_neg (by omega), if_pos (by split_ifs at hw <;> omega)]

theorem final_labels {n m ℓ : ℕ} (c : Cost n m) (i : Fin n)
    (P : CopyPacking n m (2 ^ ℓ) ℓ) (hP : CopyFeasible c i P) :
    ∃ p : Labels n m (2 ^ ℓ), ValidPacking c i p ∧ excludedCount p ≤ P.marked.card := by
  classical
  have h11 : 2 ^ ℓ / 2 ^ ℓ = 1 := Nat.div_self (by positivity)
  let z : Fin (2 ^ ℓ / 2 ^ ℓ) := ⟨0, by rw [h11]; exact one_pos⟩
  have hz : ∀ k : Fin (2 ^ ℓ / 2 ^ ℓ), k = z := fun k => Fin.ext (by
    have : k.val < 1 := h11 ▸ k.isLt
    show k.val = 0
    omega)
  have hloc : ∀ s, (P.location s).val < binCount n (2 ^ ℓ) := fun s =>
    loc_lt_binCount _ (hP.2 s)
  let p : Labels n m (2 ^ ℓ) := fun r =>
    if h : 0 < r.val then
      (if ((⟨r, h⟩, z) : Copies m (2 ^ ℓ) ℓ) ∈ P.marked then none
        else some ⟨(P.location (⟨r, h⟩, z)).val, hloc _⟩)
    else none
  refine ⟨p, ⟨fun r hr => ?_, fun w => ?_⟩, ?_⟩
  · simp [p, hr]
  · let v : Fin (stageBins n ℓ) :=
      ⟨w.val, lt_of_lt_of_le w.isLt (binCount_le_stageBins n ℓ)⟩
    rw [binCapacity_eq v w rfl]
    refine le_trans (le_of_eq ?_) (hP.1 v)
    unfold copyLoad
    rw [Fintype.sum_prod_type]
    have hin : ∀ x : {r : Fin (m / 2 ^ ℓ) // 0 < r.val},
        (∑ k : Fin (2 ^ ℓ / 2 ^ ℓ), (if P.location (x, k) = v ∧ (x, k) ∉ P.marked
          then representativeCost c i (2 ^ ℓ) (x, k).1.val else 0)) =
        (if p x.1 = some w then representativeCost c i (2 ^ ℓ) x.1 else 0) := by
      intro x
      rw [sum_eq_single z (fun k _ hk => absurd (hz k) hk) (fun h => absurd (mem_univ z) h)]
      have hp : p x.1 = (if ((x, z) : Copies m (2 ^ ℓ) ℓ) ∈ P.marked then none
          else some ⟨(P.location (x, z)).val, hloc _⟩) := by
        simp only [p, dif_pos x.2]
      rw [hp]
      by_cases hm : ((x, z) : Copies m (2 ^ ℓ) ℓ) ∈ P.marked
      · simp [hm]
      · simp only [hm, if_false, not_false_eq_true, and_true]
        congr 1
        apply propext
        simp only [Option.some.injEq, Fin.ext_iff, v]
    rw [Fintype.sum_congr _ _ hin]
    rw [← sum_subtype (univ.filter (fun r : Fin (m / 2 ^ ℓ) => 0 < r.val)) (by simp)
      (fun r => if p r = some w then representativeCost c i (2 ^ ℓ) r else 0)]
    rw [sum_filter_of_ne]
    intro r _ hne
    by_contra h0
    apply hne
    have : p r = none := by simp [p, h0]
    simp [this]
  · unfold excludedCount
    have hsub : univ.filter (fun r : Fin (m / 2 ^ ℓ) => 0 < r.val ∧ p r = none) ⊆
        P.marked.image (fun s => s.1.1) := by
      intro r hr
      simp only [mem_filter, mem_univ, true_and] at hr
      obtain ⟨h0, hn⟩ := hr
      apply mem_image.mpr
      refine ⟨(⟨r, h0⟩, z), ?_, rfl⟩
      by_contra hm
      simp [p, h0, hm] at hn
    exact le_trans (card_le_card hsub) card_image_le

/-! ### Halving: merging paired bins -/
lemma pair_map_core {B B' : ℕ} (π : Fin B → Fin B) (hπ : IsPairing π) (X : Finset (Fin B))
    (cap : Fin B → ℝ) (cap' : Fin B' → ℝ) (a' : ℕ)
    (hX : ∀ v ∈ X, π v ∈ X) (hX2 : ∀ u ∈ X, ∀ v ∈ X, u = v ∨ u = π v)
    (ha'B : a' ≤ B') (hXB : ∀ v ∈ X, a' < B')
    (hXcap : ∀ v ∈ X, ∀ h : a' < B', (cap v + cap (π v)) / 2 ≤ cap' ⟨a', h⟩)
    (hNcap : ∀ v, v ∉ X → cap v = 1) (hcap' : ∀ w : Fin B', w.val < a' → cap' w = 1)
    (hcard : (univ.filter (fun v => v ∉ X)).card ≤ 2 * a') :
    ∃ φ : Fin B → Fin B', (∀ v, φ (π v) = φ v) ∧ (∀ u v, φ u = φ v → u = v ∨ u = π v) ∧
      (∀ v, (cap v + cap (π v)) / 2 ≤ cap' (φ v)) := by
  classical
  have hinv := hπ.1
  have hfix := hπ.2
  have hXc : ∀ v, v ∉ X → π v ∉ X := fun v hv h => hv (by have := hX _ h; rwa [hinv v] at this)
  set L := univ.filter (fun v => v ∉ X ∧ v < π v) with hL
  have hLcard : L.card ≤ a' := by
    have hdisj : Disjoint L (L.image π) := by
      rw [Finset.disjoint_left]
      intro v hv hv'
      obtain ⟨u, hu, rfl⟩ := mem_image.mp hv'
      simp only [hL, mem_filter, mem_univ, true_and] at hv hu
      rw [hinv u] at hv
      exact lt_asymm hu.2 hv.2
    have hsub : L ∪ L.image π ⊆ univ.filter (fun v => v ∉ X) := by
      intro v hv
      rcases mem_union.mp hv with h | h
      · simp only [hL, mem_filter, mem_univ, true_and] at h ⊢; exact h.1
      · obtain ⟨u, hu, rfl⟩ := mem_image.mp h
        simp only [hL, mem_filter, mem_univ, true_and] at hu ⊢; exact hXc u hu.1
    have h1 := card_le_card hsub
    rw [card_union_of_disjoint hdisj, card_image_of_injective _ hinv.injective] at h1
    omega
  let ld : Fin B → Fin B := fun v => min v (π v)
  have hld_mem : ∀ v, v ∉ X → ld v ∈ L := by
    intro v hv
    simp only [hL, mem_filter, mem_univ, true_and, ld]
    rcases lt_or_gt_of_ne (hfix v).symm with h | h
    · rw [min_eq_left h.le]; exact ⟨hv, h⟩
    · rw [min_eq_right h.le, hinv v]; exact ⟨hXc v hv, h⟩
  have hld_pi : ∀ v, ld (π v) = ld v := fun v => by simp only [ld, hinv v, min_comm]
  have hld_cases : ∀ v, ld v = v ∨ ld v = π v := fun v => min_choice _ _
  let φ : Fin B → Fin B' := fun v =>
    if h : v ∈ X then ⟨a', hXB v h⟩
    else ⟨(L.equivFin ⟨ld v, hld_mem v h⟩).val,
      lt_of_lt_of_le (lt_of_lt_of_le (L.equivFin ⟨ld v, hld_mem v h⟩).isLt hLcard) ha'B⟩
  have hφN : ∀ v (h : v ∉ X), (φ v).val = (L.equivFin ⟨ld v, hld_mem v h⟩).val := by
    intro v h; simp only [φ, dif_neg h]
  have hφX : ∀ v, v ∈ X → (φ v).val = a' := by
    intro v h; simp only [φ, dif_pos h]
  have hφlt : ∀ v, v ∉ X → (φ v).val < a' := fun v h => by
    rw [hφN v h]; exact lt_of_lt_of_le (Fin.isLt _) hLcard
  refine ⟨φ, fun v => ?_, fun u v huv => ?_, fun v => ?_⟩
  · apply Fin.ext
    by_cases h : v ∈ X
    · rw [hφX _ (hX v h), hφX v h]
    · rw [hφN _ (hXc v h), hφN v h]
      exact congrArg (fun x => (L.equivFin x).val) (Subtype.ext (hld_pi v))
  · have hv' := congrArg Fin.val huv
    by_cases hu : u ∈ X <;> by_cases hv : v ∈ X
    · exact hX2 u hu v hv
    · have := hφlt v hv; rw [hφX u hu] at hv'; omega
    · have := hφlt u hu; rw [hφX v hv] at hv'; omega
    · rw [hφN u hu, hφN v hv] at hv'
      have := congrArg Subtype.val (L.equivFin.injective (Fin.ext hv'))
      simp only at this
      rcases hld_cases u with h1 | h1 <;> rcases hld_cases v with h2 | h2
      · left; rw [← h1, this, h2]
      · right; rw [← h1, this, h2]
      · right; rw [← hinv u, ← h1, this, h2]
      · left; rw [← hinv u, ← h1, this, h2, hinv v]
  · by_cases h : v ∈ X
    · have := hXcap v h (hXB v h)
      convert this using 2
      exact Fin.ext (hφX v h)
    · rw [hNcap v h, hNcap _ (hXc v h), hcap' _ (hφlt v h)]
      norm_num

lemma pair_map_two {B B' : ℕ} (π : Fin B → Fin B) (hπ : IsPairing π) (u0 v0 : Fin B)
    (h0 : π u0 = v0) (cap : Fin B → ℝ) (cap' : Fin B' → ℝ) (a' : ℕ) (ha'B : a' < B')
    (hcap0 : (cap u0 + cap v0) / 2 ≤ cap' ⟨a', ha'B⟩)
    (hNcap : ∀ v, v ≠ u0 → v ≠ v0 → cap v = 1) (hcap' : ∀ w : Fin B', w.val < a' → cap' w = 1)
    (hcard : B ≤ 2 * a' + 2) :
    ∃ φ : Fin B → Fin B', (∀ v, φ (π v) = φ v) ∧ (∀ u v, φ u = φ v → u = v ∨ u = π v) ∧
      (∀ v, (cap v + cap (π v)) / 2 ≤ cap' (φ v)) := by
  classical
  have h1 : π v0 = u0 := by rw [← h0, hπ.1 u0]
  have hne : u0 ≠ v0 := fun h => hπ.2 u0 (h0.trans h.symm)
  apply pair_map_core π hπ {u0, v0} cap cap' a'
  · intro v hv
    simp only [mem_insert, mem_singleton] at hv ⊢
    rcases hv with rfl | rfl
    · right; exact h0
    · left; exact h1
  · intro u hu v hv
    simp only [mem_insert, mem_singleton] at hu hv
    rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
    · left; rfl
    · right; exact h1.symm
    · right; exact h0.symm
    · left; rfl
  · exact ha'B.le
  · intro _ _; exact ha'B
  · intro v hv h
    simp only [mem_insert, mem_singleton] at hv
    rcases hv with rfl | rfl
    · rw [h0]; exact hcap0
    · rw [h1, add_comm]; exact hcap0
  · intro v hv
    simp only [mem_insert, mem_singleton, not_or] at hv
    exact hNcap v hv.1 hv.2
  · exact hcap'
  · have : univ.filter (fun v => v ∉ ({u0, v0} : Finset (Fin B))) = univ \ {u0, v0} := by
      ext v; simp
    rw [this, card_univ_sdiff, card_pair hne, Fintype.card_fin]
    omega

lemma stageCapacity_eq (n j : ℕ) (v : Fin (stageBins n j)) :
    stageCapacity n j v = if v.val < n / 2 ^ j then 1 else if v.val = n / 2 ^ j then
      ((n % 2 ^ j : ℕ) : ℝ) / (2 : ℝ) ^ j else 0 := by
  unfold stageCapacity; push_cast; rfl

lemma pair_map {n j : ℕ} (π : Fin (stageBins n j) → Fin (stageBins n j)) (hπ : IsPairing π)
    (hexc : ∀ u v, ExceptionalPair n j u v → π u = v) :
    ∃ φ : Fin (stageBins n j) → Fin (stageBins n (j + 1)), (∀ v, φ (π v) = φ v) ∧
      (∀ u v, φ u = φ v → u = v ∨ u = π v) ∧
      (∀ v, (stageCapacity n j v + stageCapacity n j (π v)) / 2 ≤
        stageCapacity n (j + 1) (φ v)) := by
  classical
  have ha' : n / 2 ^ (j + 1) = n / 2 ^ j / 2 := by rw [pow_succ, Nat.div_div_eq_div_mul]
  have hr' : n % 2 ^ (j + 1) = n % 2 ^ j + 2 ^ j * (n / 2 ^ j % 2) := by
    rw [pow_succ, Nat.mod_mul]
  have hB : stageBins n j = (n / 2 ^ j + if n % 2 ^ j = 0 then 0 else 1) +
      (n / 2 ^ j + if n % 2 ^ j = 0 then 0 else 1) % 2 := rfl
  have hB' : stageBins n (j + 1) = (n / 2 ^ (j + 1) + if n % 2 ^ (j + 1) = 0 then 0 else 1) +
      (n / 2 ^ (j + 1) + if n % 2 ^ (j + 1) = 0 then 0 else 1) % 2 := rfl
  have hcap' : ∀ w : Fin (stageBins n (j + 1)), w.val < n / 2 ^ j / 2 →
      stageCapacity n (j + 1) w = 1 := by
    intro w hw; unfold stageCapacity; rw [if_pos (by rw [ha']; exact hw)]
  have hP2 : (0 : ℝ) < 2 ^ j := by positivity
  have hpj : 0 < 2 ^ j := by positivity
  set a := n / 2 ^ j with ha
  set r := n % 2 ^ j with hr
  rcases Nat.mod_two_eq_zero_or_one a with hae | hao
  · rw [hae, mul_zero, add_zero] at hr'
    by_cases hr0 : r = 0
    · -- no exceptional pair: all bins are unit bins
      rw [if_pos hr0] at hB
      apply pair_map_core π hπ ∅ _ _ (a / 2)
      · simp
      · simp
      · rw [hB', ha']; omega
      · simp
      · simp
      · intro v _
        rw [stageCapacity_eq, if_pos (by have := v.isLt; omega)]
      · exact hcap'
      · have : univ.filter (fun v : Fin (stageBins n j) => v ∉ (∅ : Finset _)) = univ := by
          ext v; simp
        rw [this, card_univ, Fintype.card_fin, hB]
        omega
    · rw [if_neg hr0] at hB
      have hBv : stageBins n j = a + 2 := by omega
      have hr'0 : ¬ n % 2 ^ (j + 1) = 0 := by omega
      have hlt : a / 2 < stageBins n (j + 1) := by rw [hB', if_neg hr'0, ha']; omega
      apply pair_map_two π hπ ⟨a, by omega⟩ ⟨a + 1, by omega⟩ _ _ _ (a / 2) hlt
      · rw [stageCapacity_eq, stageCapacity_eq, stageCapacity_eq]
        simp only [lt_irrefl, if_false, if_true, show ¬ a + 1 < a by omega,
          show a + 1 ≠ a by omega, ← ha, ← hr, ha', hr']
        rw [pow_succ]
        field_simp
        simp
      · intro v h1 h2
        rw [stageCapacity_eq, if_pos]
        have := v.isLt
        have h1' : v.val ≠ a := fun h => h1 (Fin.ext h)
        have h2' : v.val ≠ a + 1 := fun h => h2 (Fin.ext h)
        omega
      · exact hcap'
      · omega
      · apply hexc
        simp only [ExceptionalPair]
        rw [if_pos hae]
        exact ⟨hr0, rfl, rfl⟩
  · have hBv : stageBins n j = a + 1 := by
      split_ifs at hB <;> omega
    rw [hao, mul_one] at hr'
    have hr'0 : ¬ n % 2 ^ (j + 1) = 0 := by omega
    have hlt : a / 2 < stageBins n (j + 1) := by rw [hB', if_neg hr'0, ha']; omega
    have ha1 : 0 < a := Nat.pos_of_ne_zero (fun h => by rw [h] at hao; simp at hao)
    apply pair_map_two π hπ ⟨0, by omega⟩ ⟨a, by omega⟩ _ _ _ (a / 2) hlt
    · rw [stageCapacity_eq, stageCapacity_eq, stageCapacity_eq]
      simp only [lt_irrefl, if_false, if_true, ha1, ← ha, ← hr, ha', hr']
      push_cast
      rw [pow_succ]
      field_simp
      ring_nf
      rfl
    · intro v h1 h2
      rw [stageCapacity_eq, if_pos]
      have := v.isLt
      have h2' : v.val ≠ a := fun h => h2 (Fin.ext h)
      omega
    · exact hcap'
    · omega
    · apply hexc
      simp only [ExceptionalPair]
      rw [if_neg (by omega)]
      constructor <;> trivial

theorem halving_step {n m q j : ℕ} (hn : 0 < n) (hj : 2 ^ (j + 1) ∣ q)
    (c : Cost n m) (i : Fin n) (P : CopyPacking n m q j) (hP : CopyFeasible c i P)
    (C₃ : ℝ) (hH : HalvingOutput c i P C₃) :
    ∃ P' : CopyPacking n m q (j + 1), CopyFeasible c i P' ∧
      (P'.marked.card : ℝ) ≤ (P.marked.card : ℝ) / 2 + C₃ * Real.sqrt (stageBins n j) := by
  classical
  obtain ⟨keep, marks, π, hπ, hexc, hkcard, hmk, hmk2, hload, hmarks⟩ := hH
  obtain ⟨φ, hφπ, hφinj, hφcap⟩ := pair_map π hπ hexc
  have hqq : q / 2 ^ (j + 1) = q / 2 ^ j / 2 := by rw [pow_succ, Nat.div_div_eq_div_mul]
  let E : ∀ r : {r : Fin (m / q) // 0 < r.val},
      {x // x ∈ keep.filter (fun s => s.1 = r)} ≃ Fin (q / 2 ^ (j + 1)) :=
    fun r => (keep.filter (fun s => s.1 = r)).equivFinOfCardEq ((hkcard r).trans hqq.symm)
  let old : Copies m q (j + 1) → Copies m q j := fun t => ((E t.1).symm t.2).val
  have hold_mem : ∀ t, old t ∈ keep ∧ (old t).1 = t.1 := fun t => by
    have := ((E t.1).symm t.2).property
    simpa only [mem_filter] using this
  have hold_inj : Function.Injective old := by
    intro t t' h
    have h1 : t.1 = t'.1 := by rw [← (hold_mem t).2, ← (hold_mem t').2, h]
    obtain ⟨r, k⟩ := t
    obtain ⟨r', k'⟩ := t'
    simp only at h1
    subst h1
    have : (E r).symm k = (E r).symm k' := Subtype.ext h
    rw [(E r).symm.injective this]
  have hold_image : univ.image old = keep := by
    ext s
    constructor
    · intro hs
      obtain ⟨t, -, rfl⟩ := mem_image.mp hs
      exact (hold_mem t).1
    · intro hs
      apply mem_image.mpr
      refine ⟨(s.1, E s.1 ⟨s, by simp [hs]⟩), mem_univ _, ?_⟩
      simp [old]
  let P' : CopyPacking n m q (j + 1) :=
    { location := fun t => φ (P.location (old t))
      marked := univ.filter (fun t => old t ∈ marks) }
  have hcapnn := stageCapacity_nonneg n j
  refine ⟨P', ⟨fun w => ?_, fun t ht => ?_⟩, ?_⟩
  · unfold copyLoad
    let G : Copies m q j → ℝ := fun s =>
      if φ (P.location s) = w ∧ s ∉ marks then representativeCost c i q s.1.val else 0
    have h1 : ∀ t, (if P'.location t = w ∧ t ∉ P'.marked then
        representativeCost c i q t.1.val else 0) = G (old t) := by
      intro t
      simp only [P', G, mem_filter, mem_univ, true_and, (hold_mem t).2]
    rw [Fintype.sum_congr _ _ h1, ← sum_image (fun x _ y _ h => hold_inj h), hold_image]
    by_cases hw : ∃ v, φ v = w
    · obtain ⟨v, rfl⟩ := hw
      refine le_trans (le_of_eq ?_) (le_trans (hload v) (hφcap v))
      apply sum_congr rfl
      intro s _
      simp only [G]
      congr 1
      apply propext
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨h2, ?_⟩
        rcases hφinj _ _ h1 with h | h
        · left; exact h
        · right; exact h
      · rintro ⟨h2, h | h⟩
        · exact ⟨by rw [h], h2⟩
        · exact ⟨by rw [h, hφπ], h2⟩
    · push Not at hw
      refine le_trans (le_of_eq ?_) (stageCapacity_nonneg n (j + 1) w)
      apply sum_eq_zero
      intro s _
      simp only [G]
      rw [if_neg]
      rintro ⟨h, -⟩
      exact hw _ h
  · let v := P.location (old t)
    have h1 : stageCapacity n j v ≠ 0 := hP.2 (old t)
    have h2 : 0 < stageCapacity n j v := lt_of_le_of_ne (hcapnn v) (Ne.symm h1)
    have h3 := hcapnn (π v)
    have h4 := hφcap v
    have h5 : stageCapacity n (j + 1) (φ v) = 0 := ht
    linarith
  · have hc : P'.marked.card ≤ marks.card := by
      apply card_le_card_of_injOn old
      · intro t ht
        simpa [P'] using ht
      · exact hold_inj.injOn
    have hc' : (P'.marked.card : ℝ) ≤ marks.card := by exact_mod_cast hc
    linarith

end SublinearChoresMMS.Disposal.Dev.L31.PartU
end
end

section
noncomputable section
namespace SublinearChoresMMS.Disposal.Dev.L31
open SublinearChoresMMS.Disposal
open Finset
alias halving_step := SublinearChoresMMS.Disposal.Dev.L31.PartU.halving_step

alias final_labels := SublinearChoresMMS.Disposal.Dev.L31.PartU.final_labels

end SublinearChoresMMS.Disposal.Dev.L31
end
end

section
noncomputable section
namespace SublinearChoresMMS.Disposal.Dev.L31.PartV
open SublinearChoresMMS.Disposal
open SublinearChoresMMS.Disposal.Dev.L31
open Finset
/-- `s := √(n log n)`. -/
def sq (n : ℕ) : ℝ := Real.sqrt ((n : ℝ) * Real.log n)

lemma log_pos3 {n : ℕ} (hn : 3 ≤ n) : 1 < Real.log n := by
  have h3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have : Real.exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
  rw [Real.lt_log_iff_exp_lt (by linarith)]
  linarith

lemma sq_sq {n : ℕ} (hn : 3 ≤ n) : sq n ^ 2 = n * Real.log n := by
  have h1 := log_pos3 hn
  have h0 : (0 : ℝ) ≤ n := by positivity
  unfold sq
  rw [Real.sq_sqrt (by positivity)]

lemma one_lt_sq {n : ℕ} (hn : 3 ≤ n) : 1 < sq n := by
  have h1 := log_pos3 hn
  have h3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
  unfold sq
  rw [show (1 : ℝ) = Real.sqrt 1 by simp]
  exact Real.sqrt_lt_sqrt (by norm_num) (by nlinarith)

lemma block_le_sq {n : ℕ} (hn : 3 ≤ n) : (blockSize n : ℝ) ≤ sq n := by
  have hs := one_lt_sq hn
  have hs0 : 0 < sq n := by linarith
  set j := ⌊Real.logb 2 (sq n)⌋₊ with hj
  have hb : (blockSize n : ℝ) = (2 : ℝ) ^ (j : ℝ) := by
    unfold blockSize
    rw [Real.rpow_natCast]
    push_cast
    rfl
  have hlog0 : 0 ≤ Real.logb 2 (sq n) := Real.logb_nonneg (by norm_num) hs.le
  have hrp : (2 : ℝ) ^ Real.logb 2 (sq n) = sq n := Real.rpow_logb (by norm_num) (by norm_num) hs0
  rw [hb, ← hrp]
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (Nat.floor_le hlog0)

lemma eventually_log (D : ℝ) : ∃ N : ℕ, ∀ n : ℕ, N ≤ n → D * Real.log n ≤ n := by
  have hD : (0 : ℝ) < max D 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have h := (Real.isLittleO_log_id_atTop.comp_tendsto tendsto_natCast_atTop_atTop).bound
    (inv_pos.2 hD)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (h.and (Filter.eventually_ge_atTop 1))
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨h1, h2⟩ := hN n hn
  simp only [Function.comp, id, Real.norm_eq_abs] at h1
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hl0 : 0 ≤ Real.log n := Real.log_natCast_nonneg n
  rw [abs_of_nonneg hl0, abs_of_nonneg hn0] at h1
  have := mul_le_mul_of_nonneg_left h1 hD.le
  rw [← mul_assoc, mul_inv_cancel₀ hD.ne', one_mul] at this
  nlinarith [le_max_left D 1]

/-- For large `n`, `K * blockSize n ≤ n`. -/
lemma K_mul_block_le (K : ℕ) : ∃ N : ℕ, ∀ n : ℕ, N ≤ n → K * blockSize n ≤ n := by
  obtain ⟨N, hN⟩ := eventually_log ((K : ℝ) ^ 2)
  refine ⟨max N 3, fun n hn => ?_⟩
  have hn3 : 3 ≤ n := le_trans (le_max_right _ _) hn
  have hlog := hN n (le_trans (le_max_left _ _) hn)
  have hb := block_le_sq hn3
  have hss := sq_sq hn3
  have hs0 : 0 < sq n := by linarith [one_lt_sq hn3]
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hK0 : (0 : ℝ) ≤ K := by positivity
  have h1 : (K : ℝ) * sq n ≤ n := by
    have : ((K : ℝ) * sq n) ^ 2 ≤ (n : ℝ) ^ 2 := by
      rw [mul_pow, hss]; nlinarith
    exact (pow_le_pow_iff_left₀ (by positivity) hn0 (by norm_num)).1 this
  have : (K : ℝ) * blockSize n ≤ n := le_trans (mul_le_mul_of_nonneg_left hb hK0) h1
  exact_mod_cast this

lemma stageBins_le (n j : ℕ) : stageBins n j ≤ n / 2 ^ j + 2 := by
  unfold stageBins binCount
  dsimp only
  split_ifs <;> omega

lemma le_stageBins (n j : ℕ) : n / 2 ^ j ≤ stageBins n j := by
  unfold stageBins binCount
  dsimp only
  split_ifs <;> omega

/-- The arithmetic of one halving step. -/
lemma step_arith (a b t : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (ht : 0 ≤ t)
    (hat : a ^ 2 = 2 * t ^ 2) (hbt : b ^ 2 ≤ 2 * t ^ 2 + 2) (ht4 : 4 ≤ t ^ 2) :
    4 * a + b ≤ 8 * t := by
  have h1 : 4 * a ≤ 5.66 * t := by
    have : (4 * a) ^ 2 ≤ (5.66 * t) ^ 2 := by nlinarith
    exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by norm_num)).1 this
  have h2 : b ≤ 1.6 * t := by
    have : b ^ 2 ≤ (1.6 * t) ^ 2 := by nlinarith
    exact (pow_le_pow_iff_left₀ hb (by positivity) (by norm_num)).1 this
  linarith

theorem lemma_3_1 :
    ∃ A B : ℝ, 0 < A ∧ 0 < B ∧ ∃ n₀ : ℕ, 2 ≤ n₀ ∧
      ∀ n : ℕ, n₀ ≤ n → ∀ m : ℕ,
        blockSize n ≤ m → blockSize n ∣ m →
        ∀ c : Cost n m, Normalized c → ∀ i : Fin n,
          ∃ p : Labels n m (blockSize n), ValidPacking c i p ∧
            (excludedCount p : ℝ) ≤ A * Real.sqrt (n / blockSize n : ℕ) ∧
            (segments p : ℝ) ≤ B * (n / blockSize n : ℕ) ^ 3 := by
  obtain ⟨C₃, hC₃, b₀, hb₀, hA2⟩ := lemma_a_2
  obtain ⟨A', B', hA', hB', n₁, hn₁, hR⟩ := lemma_3_1_rearrangement
  obtain ⟨N, hN⟩ := K_mul_block_le (max b₀ 4)
  refine ⟨12 * C₃ + A', B' * (1 + 12 * C₃), by linarith, by nlinarith,
    max (max N n₁) 3, le_trans (by norm_num) (le_max_right _ _), ?_⟩
  intro n hn m hqm hqdvd c hc i
  have hnN : N ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hn₁ : n₁ ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have hn3 : 3 ≤ n := le_trans (le_max_right _ _) hn
  have hn0 : 0 < n := by omega
  set ℓ := ⌊Real.logb 2 (Real.sqrt ((n : ℝ) * Real.log n))⌋₊ with hℓ
  have hq : blockSize n = 2 ^ ℓ := rfl
  have hqpos : 0 < 2 ^ ℓ := by positivity
  have hm0 : 0 < m := by rw [hq] at hqm; omega
  have hdvd : 2 ^ ℓ ∣ m := hq ▸ hqdvd
  -- `L = n / q ≥ max b₀ 4`
  have hKq : max b₀ 4 * 2 ^ ℓ ≤ n := hq ▸ hN n hnN
  have hL : max b₀ 4 ≤ n / 2 ^ ℓ := (Nat.le_div_iff_mul_le hqpos).2 hKq
  have hLb : b₀ ≤ n / 2 ^ ℓ := le_trans (le_max_left _ _) hL
  have hL4 : 4 ≤ n / 2 ^ ℓ := le_trans (le_max_right _ _) hL
  have hC0 : 0 ≤ C₃ := by linarith
  -- real lower bound: `n / 2^k ≥ 4` for `k ≤ ℓ`
  have hreal : ∀ k, k ≤ ℓ → (4 : ℝ) ≤ (n : ℝ) / (2 : ℝ) ^ k := by
    intro k hk
    have h1 : ((n / 2 ^ ℓ : ℕ) : ℝ) ≤ (n : ℝ) / ((2 ^ ℓ : ℕ) : ℝ) := Nat.cast_div_le
    have h2 : (4 : ℝ) ≤ ((n / 2 ^ ℓ : ℕ) : ℝ) := by exact_mod_cast hL4
    have h3 : (2 : ℝ) ^ k ≤ (2 : ℝ) ^ ℓ := pow_le_pow_right₀ (by norm_num) hk
    have h4 : (n : ℝ) / (2 : ℝ) ^ ℓ ≤ (n : ℝ) / (2 : ℝ) ^ k :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) h3
    push_cast at h1
    linarith
  -- the induction over stages
  have key : ∀ j, j ≤ ℓ → ∃ P : CopyPacking n m (2 ^ ℓ) j, CopyFeasible c i P ∧
      (P.marked.card : ℝ) ≤ 8 * C₃ * Real.sqrt ((n : ℝ) / ((2 ^ j : ℕ) : ℝ)) := by
    intro j
    induction j with
    | zero =>
      intro _
      obtain ⟨P, hP, hm⟩ := initial_packing hn0 hqpos hdvd c hc i
      refine ⟨P, hP, ?_⟩
      rw [hm]; simp only [Finset.card_empty, Nat.cast_zero]; positivity
    | succ j ih =>
      intro hj
      have hjl : j < ℓ := hj
      obtain ⟨P, hP, hM⟩ := ih hjl.le
      have hsb : b₀ ≤ stageBins n j := by
        have : n / 2 ^ ℓ ≤ n / 2 ^ j :=
          Nat.div_le_div_left (Nat.pow_le_pow_right (by norm_num) hjl.le) (by positivity)
        exact le_trans hLb (le_trans this (le_stageBins n j))
      have hH := hA2 n m ℓ j hjl hn0 hm0 hdvd hsb c hc i P hP hM
      obtain ⟨P', hP', hM'⟩ := halving_step hn0 (pow_dvd_pow 2 hj) c i P hP C₃ hH
      refine ⟨P', hP', le_trans hM' ?_⟩
      -- arithmetic
      set x : ℝ := (n : ℝ) / (2 : ℝ) ^ (j + 1) with hx
      have hx4 : 4 ≤ x := hreal (j + 1) hj
      have hx0 : 0 ≤ x := by linarith
      set a := Real.sqrt ((n : ℝ) / ((2 ^ j : ℕ) : ℝ)) with ha
      set b := Real.sqrt (stageBins n j : ℝ) with hb
      set t := Real.sqrt x with ht
      have hnj : (n : ℝ) / ((2 ^ j : ℕ) : ℝ) = 2 * x := by
        rw [hx]; push_cast; rw [pow_succ]; field_simp
      have hat : a ^ 2 = 2 * t ^ 2 := by
        rw [ha, ht, Real.sq_sqrt (by positivity), Real.sq_sqrt hx0, hnj]
      have hbt : b ^ 2 ≤ 2 * t ^ 2 + 2 := by
        rw [hb, ht, Real.sq_sqrt (by positivity), Real.sq_sqrt hx0]
        have h1 : (stageBins n j : ℝ) ≤ ((n / 2 ^ j : ℕ) : ℝ) + 2 := by
          exact_mod_cast stageBins_le n j
        have h2 : ((n / 2 ^ j : ℕ) : ℝ) ≤ (n : ℝ) / ((2 ^ j : ℕ) : ℝ) := Nat.cast_div_le
        rw [hnj] at h2
        linarith
      have ht4 : 4 ≤ t ^ 2 := by rw [ht, Real.sq_sqrt hx0]; exact hx4
      have hfin := step_arith a b t (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
        (Real.sqrt_nonneg _) hat hbt ht4
      have hgoal : Real.sqrt ((n : ℝ) / ((2 ^ (j + 1) : ℕ) : ℝ)) = t := by
        rw [ht, hx]; push_cast; rfl
      rw [hgoal]
      nlinarith
  obtain ⟨P, hP, hM⟩ := key ℓ le_rfl
  obtain ⟨p, hp, hex⟩ := final_labels (ℓ := ℓ) c i P hP
  -- bound on the excluded count via `L`
  set L : ℕ := n / 2 ^ ℓ with hLdef
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (by omega : 1 ≤ L)
  have hnq : (n : ℝ) / ((2 ^ ℓ : ℕ) : ℝ) ≤ 2 * L := by
    have hlt : n < L * 2 ^ ℓ + 2 ^ ℓ := Nat.lt_div_mul_add hqpos
    have hlt' : (n : ℝ) ≤ ((L : ℝ) + 1) * ((2 ^ ℓ : ℕ) : ℝ) := by
      have : n ≤ (L + 1) * 2 ^ ℓ := by rw [add_mul, one_mul]; omega
      exact_mod_cast this
    rw [div_le_iff₀ (by positivity)]
    nlinarith [show (1 : ℝ) ≤ ((2 ^ ℓ : ℕ) : ℝ) by exact_mod_cast hqpos]
  have hsqrt2 : Real.sqrt (2 * (L : ℝ)) ≤ 1.5 * Real.sqrt L := by
    rw [Real.sqrt_mul (by norm_num)]
    have : Real.sqrt 2 ≤ 1.5 := by
      rw [Real.sqrt_le_left (by norm_num)]; norm_num
    exact mul_le_mul_of_nonneg_right this (Real.sqrt_nonneg _)
  have hex1 : (excludedCount p : ℝ) ≤ 12 * C₃ * Real.sqrt L := by
    have h1 : (excludedCount p : ℝ) ≤ P.marked.card := by exact_mod_cast hex
    have h2 : Real.sqrt ((n : ℝ) / ((2 ^ ℓ : ℕ) : ℝ)) ≤ 1.5 * Real.sqrt L :=
      le_trans (Real.sqrt_le_sqrt hnq) hsqrt2
    have h3 := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 8 * C₃)
    linarith
  obtain ⟨p', hp', hex', hseg'⟩ := hR n hn₁ m hqm hqdvd c hc i p hp
  replace hex1 : (excludedCount (n := n) (m := m) (q := blockSize n) p : ℝ) ≤
      12 * C₃ * Real.sqrt L := hex1
  refine ⟨p', hp', ?_, ?_⟩
  · have : ((n / blockSize n : ℕ) : ℝ) = L := rfl
    rw [this] at hex' ⊢
    have h6 : (12 * C₃ + A') * Real.sqrt L = 12 * C₃ * Real.sqrt L + A' * Real.sqrt L := by ring
    rw [h6]
    linarith
  · have : ((n / blockSize n : ℕ) : ℝ) = L := rfl
    rw [this] at hseg' ⊢
    have hsL : Real.sqrt L ≤ (L : ℝ) ^ 3 := by
      rw [Real.sqrt_le_left (by positivity)]
      have h7 : (L : ℝ) ≤ (L : ℝ) ^ 3 := le_self_pow₀ hL1 (by norm_num)
      have h8 : (L : ℝ) ^ 3 ≤ ((L : ℝ) ^ 3) ^ 2 := le_self_pow₀ (le_trans hL1 h7) (by norm_num)
      linarith
    have : (excludedCount p : ℝ) ≤ 12 * C₃ * (L : ℝ) ^ 3 :=
      le_trans hex1 (mul_le_mul_of_nonneg_left hsL (by positivity))
    have h4 : (B' : ℝ) * ((L : ℝ) ^ 3 + excludedCount p) ≤ B' * ((L : ℝ) ^ 3 + 12 * C₃ * L ^ 3) :=
      mul_le_mul_of_nonneg_left (by linarith) hB'.le
    have h5 : B' * ((L : ℝ) ^ 3 + 12 * C₃ * L ^ 3) = B' * (1 + 12 * C₃) * (L : ℝ) ^ 3 := by ring
    calc (segments p' : ℝ) ≤ _ := hseg'
      _ ≤ _ := h4
      _ = _ := h5

end SublinearChoresMMS.Disposal.Dev.L31.PartV
end
end

section
noncomputable section
namespace SublinearChoresMMS.Disposal.Dev.L31
open SublinearChoresMMS.Disposal
open Finset
/-! ## Part V: assembly -/
alias lemma_3_1 := SublinearChoresMMS.Disposal.Dev.L31.PartV.lemma_3_1

end SublinearChoresMMS.Disposal.Dev.L31
end
end

section
noncomputable section
open SublinearChoresMMS
open SublinearChoresMMS.Disposal
open SublinearChoresMMS.Disposal.Dev
open SublinearChoresMMS.Disposal.Dev.L31
open SublinearChoresMMS.Disposal
open Finset
theorem solution :
    ∃ A B : ℝ, 0 < A ∧ 0 < B ∧ ∃ n₀ : ℕ, 2 ≤ n₀ ∧
      ∀ n : ℕ, n₀ ≤ n → ∀ m : ℕ,
        blockSize n ≤ m → blockSize n ∣ m →
        ∀ c : Cost n m, Normalized c → ∀ i : Fin n,
          ∃ p : Labels n m (blockSize n), ValidPacking c i p ∧
            (excludedCount p : ℝ) ≤ A * Real.sqrt (n / blockSize n : ℕ) ∧
            (segments p : ℝ) ≤ B * (n / blockSize n : ℕ) ^ 3 := by
  exact SublinearChoresMMS.Disposal.Dev.L31.lemma_3_1
end
end
