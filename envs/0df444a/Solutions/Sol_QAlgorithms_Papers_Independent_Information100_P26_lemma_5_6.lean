-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P26.lemma_5_6
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T16:49:18.813197+00:00
-- url     : https://prove2.me/submissions/b01ce084-d041-4228-9cf1-109ce8a80198

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P26

noncomputable section

open scoped Matrix ComplexOrder ComplexConjugate BigOperators


namespace X6P26B

open QAlgorithms.Papers.Independent.Information100.P26

attribute [local instance] Classical.propDecidable Classical.decEq

def In {d : ℕ} (b : Blocks d) (k : Fin b.count) (i : Fin d) : Prop :=
  offset b k ≤ i.val ∧ i.val < offset b k + b.size k

theorem split_sum {n : ℕ} (k : Fin n) (f : Fin n → ℕ) (P : Fin n → Prop) [DecidablePred P] :
    (∑ j, if P j ∨ j = k then f j else 0) =
      (∑ j, if P j ∧ j ≠ k then f j else 0) + f k := by
  have hk : f k = ∑ j, (if j = k then f j else 0) := by simp
  rw [hk, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases h2 : j = k
  · subst h2; simp
  · simp [h2]

theorem offset_lt {d : ℕ} (b : Blocks d) {k k' : Fin b.count} (h : k < k') :
    offset b k + b.size k ≤ offset b k' := by
  unfold offset
  have : (∑ j : Fin b.count, if j < k then b.size j else 0) + b.size k =
      ∑ j : Fin b.count, if j < k ∨ j = k then b.size j else 0 := by
    rw [split_sum k b.size (· < k)]
    congr 1; refine Finset.sum_congr rfl fun j _ => ?_
    by_cases h1 : j < k
    · simp [h1, h1.ne]
    · simp [h1]
  rw [this]
  refine Finset.sum_le_sum fun j _ => ?_
  split_ifs with h1 h2 <;> try omega

theorem offset_succ {d : ℕ} (b : Blocks d) (k k' : Fin b.count) (h : k'.val = k.val + 1) :
    offset b k' = offset b k + b.size k := by
  unfold offset
  have e1 : ∀ j : Fin b.count, j < k' ↔ (j < k ∨ j = k) := by
    intro j; rw [Fin.lt_def, h, Fin.lt_def, Fin.ext_iff]; omega
  simp only [e1]
  rw [split_sum k b.size (· < k)]
  congr 1; refine Finset.sum_congr rfl fun j _ => ?_
  by_cases h1 : j < k
  · simp [h1, h1.ne]
  · simp [h1]

theorem offset_last {d : ℕ} (b : Blocks d) (k : Fin b.count) (h : k.val + 1 = b.count) :
    offset b k + b.size k = d := by
  refine Eq.trans ?_ b.total
  unfold offset
  have hk : b.size k = ∑ j, (if j = k then b.size j else 0) := by simp
  rw [hk, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases h1 : j < k
  · simp [h1, h1.ne]
  · by_cases h2 : j = k
    · subst h2; simp
    · exfalso; have := Fin.lt_def.not.1 h1; have := j.isLt; exact h2 (Fin.ext (by omega))

theorem offset_add_le {d : ℕ} (b : Blocks d) (k : Fin b.count) : offset b k + b.size k ≤ d := by
  by_cases h : k.val + 1 = b.count
  · exact (offset_last b k h).le
  · let l : Fin b.count := ⟨b.count - 1, by have := b.count_pos; omega⟩
    have hl : k < l := Fin.lt_def.2 (by simp [l]; have := k.isLt; omega)
    have := offset_lt b hl
    have := offset_last b l (by simp [l]; have := b.count_pos; omega)
    omega

theorem In_uniq {d : ℕ} (b : Blocks d) {k k' : Fin b.count} {i : Fin d} (h : In b k i)
    (h' : In b k' i) : k = k' := by
  rcases lt_trichotomy k k' with hk | hk | hk
  · have := offset_lt b hk; unfold In at *; omega
  · exact hk
  · have := offset_lt b hk; unfold In at *; omega

theorem offset_zero {d : ℕ} (b : Blocks d) (k : Fin b.count) (h : k.val = 0) : offset b k = 0 := by
  unfold offset
  refine Finset.sum_eq_zero fun j _ => ?_
  have : ¬ j < k := by rw [Fin.lt_def]; omega
  simp [this]

theorem exists_In {d : ℕ} (b : Blocks d) (i : Fin d) : ∃ k, In b k i := by
  let k0 : Fin b.count := ⟨0, b.count_pos⟩
  let S := Finset.univ.filter (fun k : Fin b.count => offset b k ≤ i.val)
  have hS : S.Nonempty := ⟨k0, by simp [S, offset_zero b k0 rfl]⟩
  let k := S.max' hS
  have hk : offset b k ≤ i.val := by
    have := S.max'_mem hS; simp [S] at this; exact this
  refine ⟨k, hk, ?_⟩
  by_cases h : k.val + 1 = b.count
  · rw [offset_last b k h]; exact i.isLt
  · let k' : Fin b.count := ⟨k.val + 1, by have := k.isLt; omega⟩
    have hk' : k' ∉ S := fun hm => by
      have := S.le_max' k' hm
      rw [Fin.le_def] at this; simp [k'] at this; omega
    simp [S] at hk'
    rw [← offset_succ b k k' rfl]; exact hk'

def e {d : ℕ} (b : Blocks d) (k : Fin b.count) (a : Fin (b.size k)) : Fin d :=
  ⟨offset b k + a.val, by have := offset_add_le b k; have := a.isLt; omega⟩

theorem e_val {d : ℕ} (b : Blocks d) (k : Fin b.count) (a : Fin (b.size k)) :
    (e b k a).val = offset b k + a.val := rfl

theorem e_inj {d : ℕ} (b : Blocks d) (k : Fin b.count) : Function.Injective (e b k) := by
  intro a c h; have := congrArg Fin.val h; simp [e_val] at this; exact Fin.ext this

theorem In_e {d : ℕ} (b : Blocks d) (k : Fin b.count) (a : Fin (b.size k)) : In b k (e b k a) := by
  unfold In; rw [e_val]; have := a.isLt; omega

theorem In_iff {d : ℕ} (b : Blocks d) (k : Fin b.count) (i : Fin d) :
    In b k i ↔ ∃ a, e b k a = i := by
  constructor
  · intro h; refine ⟨⟨i.val - offset b k, by unfold In at h; omega⟩, Fin.ext ?_⟩
    rw [e_val]; unfold In at h; simp; omega
  · rintro ⟨a, rfl⟩; exact In_e b k a

theorem sum_e {d : ℕ} (b : Blocks d) (k : Fin b.count) {M : Type*} [AddCommMonoid M]
    (f : Fin d → M) (hf : ∀ i, ¬ In b k i → f i = 0) :
    ∑ i, f i = ∑ a, f (e b k a) := by
  rw [show ∑ a, f (e b k a) = ∑ x ∈ Finset.univ.map ⟨e b k, e_inj b k⟩, f x from
    by rw [Finset.sum_map]; rfl]
  symm
  refine Finset.sum_subset (Finset.subset_univ _) fun i _ hi => hf i fun h => hi ?_
  obtain ⟨a, rfl⟩ := (In_iff b k i).1 h
  simp

theorem includeBlock_e {d : ℕ} (b : Blocks d) (k : Fin b.count) (t : Map (b.size k))
    (i j a c : Fin (b.size k)) :
    includeBlock b k t (e b k i, e b k j) (e b k a, e b k c) = t (i, j) (a, c) := by
  unfold includeBlock
  simp only [e_val, Nat.add_left_cancel_iff, ← Fin.ext_iff]
  simp [Finset.sum_ite_eq, Finset.sum_ite_eq', ite_and]

theorem includeBlock_zero {d : ℕ} (b : Blocks d) (k : Fin b.count) (t : Map (b.size k))
    (p q : Fin d × Fin d) (h : ¬ (In b k p.1 ∧ In b k p.2 ∧ In b k q.1 ∧ In b k q.2)) :
    includeBlock b k t p q = 0 := by
  unfold includeBlock
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ =>
    Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun c _ => ?_
  rw [if_neg]
  rintro ⟨h1, h2, h3, h4⟩
  apply h
  refine ⟨(In_iff b k _).2 ⟨i, Fin.ext ?_⟩, (In_iff b k _).2 ⟨j, Fin.ext ?_⟩,
    (In_iff b k _).2 ⟨a, Fin.ext ?_⟩, (In_iff b k _).2 ⟨c, Fin.ext ?_⟩⟩ <;> simp [e_val, *]

theorem restrictBlock_apply {d : ℕ} (b : Blocks d) (k : Fin b.count) (t : Map d)
    (i j a c : Fin (b.size k)) :
    restrictBlock b k t (i, j) (a, c) = t (e b k i, e b k j) (e b k a, e b k c) := by
  unfold restrictBlock
  have key : ∀ (x : Fin d) (y : Fin (b.size k)), (x.val = offset b k + y.val) ↔ x = e b k y := by
    intro x y; rw [Fin.ext_iff, e_val]
  simp only [key]
  simp [Finset.sum_ite_eq, Finset.sum_ite_eq', ite_and]

theorem blockSum_e {d : ℕ} (b : Blocks d) (s : (k : Fin b.count) → Map (b.size k))
    (k : Fin b.count) (i j a c : Fin (b.size k)) :
    blockSum b s (e b k i, e b k j) (e b k a, e b k c) = s k (i, j) (a, c) := by
  unfold blockSum
  simp only [Matrix.sum_apply]
  rw [Finset.sum_eq_single k]
  · exact includeBlock_e b k (s k) i j a c
  · intro k' _ hk'
    apply includeBlock_zero
    rintro ⟨h1, -⟩
    exact hk' (In_uniq b h1 (In_e b k i))
  · simp

theorem blockSum_zero {d : ℕ} (b : Blocks d) (s : (k : Fin b.count) → Map (b.size k))
    (p q : Fin d × Fin d) (h : ¬ ∃ k, In b k p.1 ∧ In b k p.2 ∧ In b k q.1 ∧ In b k q.2) :
    blockSum b s p q = 0 := by
  unfold blockSum
  simp only [Matrix.sum_apply]
  exact Finset.sum_eq_zero fun k _ => includeBlock_zero b k _ p q fun hk => h ⟨k, hk⟩

end X6P26B

open scoped Matrix ComplexOrder ComplexConjugate BigOperators

namespace X6P26C

open QAlgorithms.Papers.Independent.Information100.P26

theorem applyMap_apply {d : ℕ} (t : Map d) (X : Mat d) (i j : Fin d) :
    applyMap t X i j = ∑ r, t (i, j) r * X r.1 r.2 := by
  simp [applyMap, QAlgorithms.act, Matrix.mulVec, dotProduct]

theorem applyMap_single {d : ℕ} (t : Map d) (i j k l : Fin d) :
    applyMap t (Matrix.single k l 1) i j = t (i, j) (k, l) := by
  rw [applyMap_apply, Finset.sum_eq_single (k, l)]
  · simp
  · intro b _ hb
    simp only [Matrix.single_apply]
    rw [if_neg]; · simp
    rintro ⟨h1, h2⟩; exact hb (Prod.ext h1.symm h2.symm)
  · simp

theorem kraus_entry {d : ℕ} (t : Map d) (ht : QAlgorithms.IsChannel (applyMap t)) :
    ∃ m, ∃ E : Fin m → Mat d, (∑ a, (E a)ᴴ * E a = 1) ∧
      ∀ i j k l, t (i, j) (k, l) = ∑ a, E a i k * conj (E a j l) := by
  obtain ⟨m, E, hE, hΦ⟩ := ht
  refine ⟨m, E, hE, fun i j k l => ?_⟩
  have := congrFun (congrFun (hΦ (Matrix.single k l 1)) i) j
  rw [applyMap_single] at this
  rw [this]
  simp [QAlgorithms.krausApply, Matrix.sum_apply, Matrix.mul_apply, Matrix.single_apply,
    Matrix.conjTranspose_apply, ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq', ite_mul]

end X6P26C

open scoped Matrix ComplexOrder ComplexConjugate BigOperators


namespace X6P26M

open QAlgorithms.Papers.Independent.Information100.P26 X6P26B X6P26C

attribute [local instance] Classical.propDecidable Classical.decEq

def Blk {d : ℕ} (b : Blocks d) (t : Map d) : Prop :=
  ∀ p q : Fin d × Fin d, t p q ≠ 0 → ∃ k, In b k p.1 ∧ In b k p.2 ∧ In b k q.1 ∧ In b k q.2

theorem proj_apply {d : ℕ} (b : Blocks d) (k : Fin b.count) (i j : Fin d) :
    blockProjection b k i j = if i = j ∧ In b k i then 1 else 0 := by
  unfold blockProjection In; split_ifs <;> simp_all

theorem mul_proj {d : ℕ} (b : Blocks d) (k : Fin b.count) (M : Matrix (Fin d) (Fin d) ℂ)
    (i j : Fin d) : (M * blockProjection b k) i j = if In b k j then M i j else 0 := by
  rw [Matrix.mul_apply]
  simp only [proj_apply]
  rw [Finset.sum_eq_single j]
  · by_cases h : In b k j <;> simp [h]
  · intro l _ hl; simp [hl]
  · simp

theorem proj_mul {d : ℕ} (b : Blocks d) (k : Fin b.count) (M : Matrix (Fin d) (Fin d) ℂ)
    (i j : Fin d) : (blockProjection b k * M) i j = if In b k i then M i j else 0 := by
  rw [Matrix.mul_apply]
  simp only [proj_apply]
  rw [Finset.sum_eq_single i]
  · by_cases h : In b k i <;> simp [h]
  · intro l _ hl; simp [Ne.symm hl]
  · simp

theorem applyMap_proj {d : ℕ} (b : Blocks d) (k : Fin b.count) (t : Map d) (x y : Fin d) :
    applyMap t (blockProjection b k) x y = ∑ a, t (x, y) (e b k a, e b k a) := by
  rw [applyMap_apply, Fintype.sum_prod_type]
  simp only [proj_apply]
  have : ∀ a' : Fin d, (∑ c, t (x, y) (a', c) * (if a' = c ∧ In b k a' then 1 else 0)) =
      if In b k a' then t (x, y) (a', a') else 0 := by
    intro a'
    rw [Finset.sum_eq_single a']
    · by_cases h : In b k a' <;> simp [h]
    · intro c _ hc; simp [Ne.symm hc]
    · simp
  simp only [this]
  rw [sum_e b k _ (fun i hi => by simp [hi])]
  simp [In_e]

theorem applyMap_one' {n : ℕ} (s : Map n) (i j : Fin n) :
    applyMap s 1 i j = ∑ a, s (i, j) (a, a) := by
  rw [applyMap_apply, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_eq_single a]
  · simp
  · intro c _ hc; simp [Matrix.one_apply, Ne.symm hc]
  · simp

theorem applyMap_add {d : ℕ} (t : Map d) (X Y : Matrix (Fin d) (Fin d) ℂ) :
    applyMap t (X + Y) = applyMap t X + applyMap t Y := by
  ext i j; simp [applyMap_apply, mul_add, Finset.sum_add_distrib]

theorem applyMap_smul {d : ℕ} (t : Map d) (c : ℂ) (X : Matrix (Fin d) (Fin d) ℂ) :
    applyMap t (c • X) = c • applyMap t X := by
  ext i j; simp [applyMap_apply, Finset.mul_sum]; refine Finset.sum_congr rfl fun r _ => by ring

theorem applyMap_zero {d : ℕ} (t : Map d) : applyMap t 0 = 0 := by
  ext i j; simp [applyMap_apply]

theorem comm_of_blk {d : ℕ} (b : Blocks d) (t : Map d) (ht : Blk b t)
    (X : Matrix (Fin d) (Fin d) ℂ) : applyMap t X ∈ commutant (blockAlgebra b : Set (Mat d)) := by
  intro Y hY
  change Y ∈ blockAlgebra b at hY
  refine Submodule.span_induction (p := fun (Y : Mat d) _ => applyMap t X * Y = Y * applyMap t X)
    ?_ ?_ ?_ ?_ hY
  · rintro Y ⟨k, rfl⟩
    ext i j
    rw [mul_proj, proj_mul]
    by_cases hi : In b k i <;> by_cases hj : In b k j <;> simp only [hi, hj, if_true, if_false]
    all_goals
      have hz : ∑ r : Fin d × Fin d, t (i, j) r * X r.1 r.2 = 0 := by
        refine Finset.sum_eq_zero fun r _ => ?_
        by_cases hr : t (i, j) r = 0
        · simp [hr]
        exfalso
        obtain ⟨k', h1, h2, -, -⟩ := ht _ _ hr
        first
          | exact hj (In_uniq b h1 hi ▸ h2)
          | exact hi (In_uniq b h2 hj ▸ h1)
      rw [applyMap_apply, hz]
  · simp
  · intro Y Z _ _ h1 h2; rw [mul_add, add_mul, h1, h2]
  · intro c Y _ h; rw [Matrix.mul_smul, Matrix.smul_mul, h]

theorem fixes_of {d : ℕ} (b : Blocks d) (t : Map d)
    (hP : ∀ k, applyMap t (blockProjection b k) = blockProjection b k) :
    Fixes t (blockAlgebra b) := by
  intro X hX
  induction hX using Submodule.span_induction with
  | mem Y hY => obtain ⟨k, rfl⟩ := hY; exact hP k
  | zero => exact applyMap_zero t
  | add Y Z _ _ h1 h2 => rw [applyMap_add, h1, h2]
  | smul c Y _ h => rw [applyMap_smul, h]

theorem blk_blockSum {d : ℕ} (b : Blocks d) (s : (k : Fin b.count) → Map (b.size k)) :
    Blk b (blockSum b s) := by
  intro p q h; by_contra h'; exact h (blockSum_zero b s p q h')

theorem forward {d : ℕ} (b : Blocks d) (s : (k : Fin b.count) → Map (b.size k))
    (hs : ∀ k, UnitalChannel (s k)) : Compatible (blockAlgebra b) (blockSum b s) := by
  refine ⟨fixes_of b _ fun k => ?_, comm_of_blk b _ (blk_blockSum b s)⟩
  ext x y
  rw [applyMap_proj]
  by_cases hxy : In b k x ∧ In b k y
  · obtain ⟨i, rfl⟩ := (In_iff b k x).1 hxy.1
    obtain ⟨j, rfl⟩ := (In_iff b k y).1 hxy.2
    simp only [blockSum_e]
    rw [← applyMap_one', (hs k).2, proj_apply]
    simp [In_e, Matrix.one_apply, (e_inj b k).eq_iff]
  · rw [proj_apply, if_neg (fun (h : x = y ∧ In b k x) => hxy ⟨h.2, h.1 ▸ h.2⟩)]
    refine Finset.sum_eq_zero fun a _ => ?_
    by_contra hne
    obtain ⟨k', h1, h2, h3, -⟩ := blk_blockSum b s _ _ hne
    have := In_uniq b (In_e b k a) h3
    subst this
    exact hxy ⟨h1, h2⟩

theorem kraus_zero {d : ℕ} (b : Blocks d) (t : Map d) {m : ℕ} (E : Fin m → Mat d)
    (hK : ∀ i j k l, t (i, j) (k, l) = ∑ a, E a i k * conj (E a j l))
    (hP : ∀ k, applyMap t (blockProjection b k) = blockProjection b k)
    (n : Fin m) (k : Fin b.count) (i : Fin d) (a : Fin (b.size k)) (hi : ¬ In b k i) :
    E n i (e b k a) = 0 := by
  have h1 := congrFun (congrFun (hP k) i) i
  rw [applyMap_proj, proj_apply, if_neg (fun h => hi h.2)] at h1
  simp only [hK, Complex.mul_conj] at h1
  have h2 : (∑ a : Fin (b.size k), ∑ n : Fin m, Complex.normSq (E n i (e b k a))) = 0 := by
    exact_mod_cast h1
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => Finset.sum_nonneg fun _ _ =>
    Complex.normSq_nonneg _)] at h2
  have h3 := h2 a (Finset.mem_univ _)
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => Complex.normSq_nonneg _)] at h3
  exact Complex.normSq_eq_zero.1 (h3 n (Finset.mem_univ _))

theorem kraus_zero' {d : ℕ} (b : Blocks d) (t : Map d) {m : ℕ} (E : Fin m → Mat d)
    (hK : ∀ i j k l, t (i, j) (k, l) = ∑ a, E a i k * conj (E a j l))
    (hP : ∀ k, applyMap t (blockProjection b k) = blockProjection b k)
    (n : Fin m) (k : Fin b.count) (i a : Fin d) (ha : In b k a) (hne : E n i a ≠ 0) :
    In b k i := by
  obtain ⟨a, rfl⟩ := (In_iff b k a).1 ha
  by_contra hi
  exact hne (kraus_zero b t E hK hP n k i a hi)

theorem blk_of {d : ℕ} (b : Blocks d) (t : Map d) {m : ℕ} (E : Fin m → Mat d)
    (hK : ∀ i j k l, t (i, j) (k, l) = ∑ a, E a i k * conj (E a j l))
    (hP : ∀ k, applyMap t (blockProjection b k) = blockProjection b k)
    (hC : ∀ X : Mat d, applyMap t X ∈ commutant (blockAlgebra b : Set (Mat d))) : Blk b t := by
  rintro ⟨i, j⟩ ⟨a, c⟩ h
  obtain ⟨k, hk⟩ := exists_In b i
  have hj : In b k j := by
    by_contra hj
    have := congrFun (congrFun (hC (Matrix.single a c 1) (blockProjection b k)
      (Submodule.subset_span ⟨k, rfl⟩)) i) j
    rw [mul_proj, proj_mul, if_neg hj, if_pos hk, applyMap_single] at this
    exact h this.symm
  rw [hK] at h
  obtain ⟨n, -, hn⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  have hia : E n i a ≠ 0 := fun h0 => hn (by simp [h0])
  have hjc : E n j c ≠ 0 := fun h0 => hn (by simp [h0])
  obtain ⟨ka, hka⟩ := exists_In b a
  obtain ⟨kc, hkc⟩ := exists_In b c
  have e1 := In_uniq b (kraus_zero' b t E hK hP n ka i a hka hia) hk
  have e2 := In_uniq b (kraus_zero' b t E hK hP n kc j c hkc hjc) hj
  exact ⟨k, hk, hj, e1 ▸ hka, e2 ▸ hkc⟩

theorem backward {d : ℕ} (b : Blocks d) (t : Map d) (ht : UnitalChannel t)
    (hc : Compatible (blockAlgebra b) t) :
    ∃ s : (k : Fin b.count) → Map (b.size k),
      (∀ k, UnitalChannel (s k)) ∧ t = blockSum b s := by
  obtain ⟨m, E, hE, hK⟩ := kraus_entry t ht.1
  have hP : ∀ k, applyMap t (blockProjection b k) = blockProjection b k :=
    fun k => hc.1 _ (Submodule.subset_span ⟨k, rfl⟩)
  have hB := blk_of b t E hK hP hc.2
  refine ⟨fun k => restrictBlock b k t, fun k => ⟨?_, ?_⟩, ?_⟩
  · let F : Fin m → Matrix (Fin (b.size k)) (Fin (b.size k)) ℂ :=
      fun n => Matrix.of fun i a => E n (e b k i) (e b k a)
    refine ⟨m, F, ?_, fun ρ => ?_⟩
    · show ∑ n, (F n)ᴴ * F n = 1
      ext a c
      have h1 := congrFun (congrFun hE (e b k a)) (e b k c)
      simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
        Matrix.one_apply, (e_inj b k).eq_iff] at h1 ⊢
      rw [← h1]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [sum_e b k _ (fun i hi => by simp [kraus_zero b t E hK hP n k i a hi])]
      rfl
    · ext i j
      rw [applyMap_apply]
      simp only [QAlgorithms.krausApply, Matrix.sum_apply, Matrix.mul_apply,
        Matrix.conjTranspose_apply, F, Matrix.of_apply, restrictBlock_apply, hK,
        Fintype.sum_prod_type, Finset.sum_mul, Finset.mul_sum]
      conv_rhs =>
        rw [Finset.sum_comm]
        enter [2, x]
        rw [Finset.sum_comm]
      conv_rhs => rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ =>
        Finset.sum_congr rfl fun n _ => ?_
      simp only [RCLike.star_def]; ring
  · ext i j
    rw [applyMap_one']
    simp only [restrictBlock_apply]
    rw [← applyMap_proj, hP k, proj_apply]
    simp [In_e, Matrix.one_apply, (e_inj b k).eq_iff]
  · ext p q
    by_cases h : ∃ k, In b k p.1 ∧ In b k p.2 ∧ In b k q.1 ∧ In b k q.2
    · obtain ⟨k, h1, h2, h3, h4⟩ := h
      obtain ⟨i, hi⟩ := (In_iff b k _).1 h1
      obtain ⟨j, hj⟩ := (In_iff b k _).1 h2
      obtain ⟨a, ha⟩ := (In_iff b k _).1 h3
      obtain ⟨c, hc⟩ := (In_iff b k _).1 h4
      obtain ⟨p1, p2⟩ := p; obtain ⟨q1, q2⟩ := q
      simp only at hi hj ha hc
      subst hi hj ha hc
      rw [blockSum_e, restrictBlock_apply]
    · rw [blockSum_zero b _ p q h]
      by_contra hne
      exact h (hB p q hne)

end X6P26M


open QAlgorithms.Papers.Independent.Information100.P26 in
theorem solution {d : ℕ} (hd : 0 < d) (b : Blocks d) (t : Map d) (ht : UnitalChannel t) :
    (∃ s : (k : Fin b.count) → Map (b.size k),
      (∀ k, UnitalChannel (s k)) ∧ t = blockSum b s) ↔ Compatible (blockAlgebra b) t := by
  constructor
  · rintro ⟨s, hs, rfl⟩; exact X6P26M.forward b s hs
  · exact X6P26M.backward b t ht

end
