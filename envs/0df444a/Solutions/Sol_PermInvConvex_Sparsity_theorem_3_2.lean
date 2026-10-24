-- Prove2me | solution 1 for PermInvConvex.Sparsity.theorem_3_2
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T06:34:14.331458+00:00
-- url     : https://prove2.me/submissions/26314b6f-fdc4-4fb6-9846-1d19c56edf1f

import Mathlib
import Definitions.Def_ModernConvex_Spectral_SDR
import Definitions.Def_PermInvConvex_Sparsity_Majorization
import Definitions.Def_PermInvConvex_Sparsity_Setting
import Theorems.Thm_ModernConvex_Spectral_majorization_principle
import Theorems.Thm_PermInvConvex_Sparsity_lemma_3_1
import Theorems.Thm_PermInvConvex_Sparsity_weak_majorization_5A9
import Theorems.Thm_PermInvConvex_Sparsity_proposition_3_4

open PermInvConvex.Sparsity ModernConvex.Spectral

namespace MainAux

/- Elementary sorting and Abel helper proofs adapted from accepted majorization-principle
submission 13309f84-3eaf-45da-a5b5-d6dcbb7d3b72. All helpers needed directly
are proved here because platform imports expose registered theorem statements only. -/

lemma main_abel (b c w : ℕ → ℝ) (n : ℕ) (hb : ∀ k, k + 1 < n → b (k + 1) ≤ b k)
    (hD : ∀ j, j < n → 0 ≤ ∑ k ∈ Finset.range j, (c k - w k)) :
    b (n - 1) * ∑ k ∈ Finset.range n, (c k - w k) ≤ ∑ k ∈ Finset.range n, b k * (c k - w k) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have ih' := ih (fun k hk => hb k (by omega)) (fun j hj => hD j (by omega))
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Nat.add_sub_cancel, mul_add]
    have hDn := hD n (by omega)
    have : b n * ∑ k ∈ Finset.range n, (c k - w k) ≤ b (n - 1) * ∑ k ∈ Finset.range n, (c k - w k) := by
      rcases Nat.eq_zero_or_pos n with h | h
      · subst h; simp
      · exact mul_le_mul_of_nonneg_right (hb (n - 1) (by omega) |>.trans_eq' (by congr 1; omega)) hDn
    linarith

/-- extension by zero of a `Fin m` vector to `ℕ` -/
noncomputable def main_ext {m : ℕ} (g : Fin m → ℝ) (k : ℕ) : ℝ :=
  if h : k < m then g ⟨k, h⟩ else 0

lemma main_ext_val {m : ℕ} (g : Fin m → ℝ) (i : Fin m) : main_ext g i = g i := by
  simp [main_ext, i.2]

lemma main_sum_ext {m : ℕ} (g : Fin m → ℝ) (j : ℕ) (hj : j ≤ m) :
    ∑ k ∈ Finset.range j, main_ext g k =
      ∑ i ∈ Finset.univ.filter (fun i : Fin m => (i : ℕ) < j), g i := by
  rw [Finset.sum_filter]
  have h1 : ∑ i : Fin m, (if (i : ℕ) < j then g i else 0) =
      ∑ i : Fin m, (fun k : ℕ => if k < j then main_ext g k else 0) (i : ℕ) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [main_ext_val]
  rw [h1, Fin.sum_univ_eq_sum_range (fun k : ℕ => if k < j then main_ext g k else 0) m,
    ← Finset.sum_filter]
  congr 1
  ext k
  simp only [Finset.mem_range, Finset.mem_filter]
  omega

lemma main_card_R {m : ℕ} (j : ℕ) (hj : j ≤ m) :
    (Finset.univ.filter (fun i : Fin m => (i : ℕ) < j)).card = j := by
  rw [Fin.card_filter_val_lt]; omega

lemma main_top {m : ℕ} (c : Fin m → ℝ) (hc : Antitone c) (s : Finset (Fin m)) (j : ℕ)
    (hs : s.card = j) :
    ∑ i ∈ s, c i ≤ ∑ i ∈ Finset.univ.filter (fun i : Fin m => (i : ℕ) < j), c i := by
  set R := Finset.univ.filter (fun i : Fin m => (i : ℕ) < j) with hR
  have hjm : j ≤ m := by rw [← hs]; simpa using Finset.card_le_univ s
  have hRc : R.card = j := main_card_R j hjm
  have hcard : (s \ R).card = (R \ s).card := by
    have h1 := Finset.card_sdiff_add_card_inter s R
    have h2 := Finset.card_sdiff_add_card_inter R s
    rw [Finset.inter_comm] at h2
    omega
  have hpq : ∀ p ∈ s \ R, ∀ q ∈ R \ s, c p ≤ c q := by
    intro p hp q hq
    simp only [Finset.mem_sdiff, hR, Finset.mem_filter, Finset.mem_univ, true_and] at hp hq
    exact hc (Fin.le_iff_val_le_val.mpr (by omega))
  have hdiff : ∑ i ∈ s \ R, c i ≤ ∑ i ∈ R \ s, c i := by
    rcases (s \ R).eq_empty_or_nonempty with he | hne
    · have : R \ s = ∅ := by
        rw [← Finset.card_eq_zero, ← hcard, he, Finset.card_empty]
      rw [he, this]
    · obtain ⟨p0, hp0, hmax⟩ := Finset.exists_max_image (s \ R) c hne
      calc ∑ i ∈ s \ R, c i ≤ (s \ R).card • c p0 := Finset.sum_le_card_nsmul _ _ _ hmax
        _ = (R \ s).card • c p0 := by rw [hcard]
        _ ≤ ∑ i ∈ R \ s, c i := Finset.card_nsmul_le_sum _ _ _ (fun q hq => hpq p0 hp0 q hq)
  rw [← Finset.sum_inter_add_sum_sdiff s R, ← Finset.sum_inter_add_sum_sdiff R s,
    Finset.inter_comm]
  linarith

lemma main_le_sumLargest {m : ℕ} (y : Fin m → ℝ) (s : Finset (Fin m)) (j : ℕ) (hs : s.card = j) :
    ∑ i ∈ s, y i ≤ sumLargest j y := by
  unfold sumLargest
  exact le_ciSup (f := fun s : {s : Finset (Fin m) // s.card = j} => ∑ i ∈ s.1, y i)
    (Set.finite_range _).bddAbove ⟨s, hs⟩

lemma main_sumLargest_le {m : ℕ} (x : Fin m → ℝ) (π : Equiv.Perm (Fin m)) (hπ : Antitone (x ∘ π))
    (j : ℕ) (hj : j ≤ m) :
    sumLargest j x ≤ ∑ k ∈ Finset.univ.filter (fun i : Fin m => (i : ℕ) < j), x (π k) := by
  unfold sumLargest
  have : Nonempty {s : Finset (Fin m) // s.card = j} :=
    ⟨⟨_, main_card_R j hj⟩⟩
  refine ciSup_le fun s => ?_
  have hc : (s.1.map π.symm.toEmbedding).card = j := by rw [Finset.card_map]; exact s.2
  have := main_top (x ∘ π) hπ _ j hc
  simpa [Finset.sum_map] using this

lemma main_sumLargest_perm {m : ℕ} (x : Fin m → ℝ) (σ : Equiv.Perm (Fin m)) (j : ℕ) (hj : j ≤ m) :
    sumLargest j (x ∘ σ) ≤ sumLargest j x := by
  conv_lhs => unfold sumLargest
  have : Nonempty {s : Finset (Fin m) // s.card = j} :=
    ⟨⟨_, main_card_R j hj⟩⟩
  refine ciSup_le fun s => ?_
  have hc : (s.1.map σ.toEmbedding).card = j := by rw [Finset.card_map]; exact s.2
  have := main_le_sumLargest x _ j hc
  simpa [Finset.sum_map] using this

lemma main_sumLargest_convex {m : ℕ} (j : ℕ) (hj : j ≤ m) (y y' : Fin m → ℝ) (a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    sumLargest j (a • y + b • y') ≤ a * sumLargest j y + b * sumLargest j y' := by
  conv_lhs => unfold sumLargest
  have : Nonempty {s : Finset (Fin m) // s.card = j} :=
    ⟨⟨_, main_card_R j hj⟩⟩
  refine ciSup_le fun s => ?_
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib, ← Finset.mul_sum]
  have h1 := main_le_sumLargest y s.1 j s.2
  have h2 := main_le_sumLargest y' s.1 j s.2
  nlinarith

lemma main_antitone_sort {m : ℕ} (x : Fin m → ℝ) : Antitone (x ∘ Tuple.sort (fun i => -x i)) := by
  intro i k hik
  have := Tuple.monotone_sort (fun i => -x i) hik
  simp only [Function.comp_apply] at this ⊢
  linarith


lemma norm_sublevel {n : ℕ} (ns : (Fin n → ℝ) → ℝ) (hns : IsPermInvNorm ns)
    (r : ℝ) : Convex ℝ {x | ns x ≤ r} := by
  intro x hx y hy a b ha hb hab
  calc
    ns (a • x + b • y) ≤ ns (a • x) + ns (b • y) := hns.add_le _ _
    _ = a * ns x + b * ns y := by rw [hns.smul, hns.smul, abs_of_nonneg ha, abs_of_nonneg hb]
    _ ≤ a * r + b * r := add_le_add (mul_le_mul_of_nonneg_left hx ha) (mul_le_mul_of_nonneg_left hy hb)
    _ = r := by rw [← add_mul, hab, one_mul]

lemma abs_le_mem_sign_hull {n : ℕ} (x y : Fin n → ℝ)
    (hxy : ∀ i, |x i| ≤ |y i|) :
    x ∈ convexHull ℝ (Set.univ.pi fun i => ({-|y i|, |y i|} : Set ℝ)) := by
  apply mem_convexHull_pi
  intro i _
  rw [convexHull_pair, segment_eq_Icc (by linarith [abs_nonneg (y i)])]
  exact abs_le.mp (hxy i)

lemma norm_mono_abs {n : ℕ} (ns : (Fin n → ℝ) → ℝ) (hns : IsSymmetricGauge ns)
    (x y : Fin n → ℝ) (hxy : ∀ i, |x i| ≤ |y i|) : ns x ≤ ns y := by
  have hs : (Set.univ.pi fun i => ({-|y i|, |y i|} : Set ℝ)) ⊆ {z | ns z ≤ ns y} := by
    intro z hz
    change ns z ≤ ns y
    apply le_of_eq
    apply hns.sign
    intro i
    have hi := hz i (Set.mem_univ i)
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hi
    rcases hi with hi | hi <;> simp [hi]
  exact convexHull_min hs (norm_sublevel ns hns.toIsPermInvNorm (ns y)) (abs_le_mem_sign_hull x y hxy)

def signMap {n : ℕ} (s : Fin n → ℝ) : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ) where
  toFun x i := s i * x i
  map_add' x y := by ext i; exact mul_add _ _ _
  map_smul' a x := by ext i; change s i * (a * x i) = a * (s i * x i); ring

lemma card_signMap_le {n : ℕ} (s x : Fin n → ℝ) : card (signMap s x) ≤ card x := by
  classical
  unfold card
  apply Finset.card_le_card
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  intro h
  exact hi (by change s i * x i = 0; rw [h, mul_zero])

lemma card_perm {n : ℕ} (σ : Equiv.Perm (Fin n)) (x : Fin n → ℝ) :
    card (x ∘ σ) = card x := by
  classical
  simp only [card, Finset.card_filter, Function.comp_apply]
  exact Equiv.sum_comp σ (fun i => if x i ≠ 0 then (1 : ℕ) else 0)

lemma hull_sign {n : ℕ} (ns : (Fin n → ℝ) → ℝ) (hns : IsSymmetricGauge ns)
    (K : ℕ) (x y : Fin n → ℝ) (hxy : ∀ i, |x i| = |y i|)
    (hx : x ∈ convexHull ℝ (NK ns K)) : y ∈ convexHull ℝ (NK ns K) := by
  classical
  let s : Fin n → ℝ := fun i => if x i = y i then 1 else -1
  have hs : ∀ i, |s i| = 1 := by intro i; dsimp [s]; split <;> norm_num
  have heq : signMap s x = y := by
    ext i
    change (if x i = y i then (1 : ℝ) else -1) * x i = y i
    split_ifs with h
    · simpa only [one_mul] using h
    · have hneg : x i = -y i := (abs_eq_abs.mp (hxy i)).resolve_left h
      simp only [neg_one_mul, hneg, neg_neg]
  rw [← heq]
  have hsubset : convexHull ℝ (NK ns K) ⊆ signMap s ⁻¹' convexHull ℝ (NK ns K) := by
    apply convexHull_min
    · intro z hz
      apply subset_convexHull ℝ (NK ns K)
      refine ⟨?_, (card_signMap_le s z).trans hz.2⟩
      have he : ns (signMap s z) = ns z := hns.sign _ _ (by
        intro i
        change |s i * z i| = |z i|
        rw [abs_mul, hs, one_mul])
      exact he.le.trans hz.1
    · exact (convex_convexHull ℝ (NK ns K)).linear_preimage (signMap s)
  exact hsubset hx

lemma hull_mono_abs {n : ℕ} (ns : (Fin n → ℝ) → ℝ) (hns : IsSymmetricGauge ns)
    (K : ℕ) (x y : Fin n → ℝ) (hxy : ∀ i, |x i| ≤ |y i|)
    (hy : y ∈ convexHull ℝ (NK ns K)) : x ∈ convexHull ℝ (NK ns K) := by
  have hs : (Set.univ.pi fun i => ({-|y i|, |y i|} : Set ℝ)) ⊆ convexHull ℝ (NK ns K) := by
    intro z hz
    apply hull_sign ns hns K y z ?_ hy
    intro i
    have hi := hz i (Set.mem_univ i)
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hi
    rcases hi with hi | hi <;> simp [hi]
  exact convexHull_min hs (convex_convexHull ℝ _) (abs_le_mem_sign_hull x y hxy)

lemma norm_weak_mono {n : ℕ} (ns : (Fin n → ℝ) → ℝ) (hns : IsSymmetricGauge ns)
    (u y : Fin n → ℝ) (hy : ∀ i, 0 ≤ y i) (h : WeakMajorizes u y) : ns y ≤ ns u := by
  obtain ⟨v, huv, hyv⟩ := weak_majorization_5A9 u y h
  have hv : ∀ i, 0 ≤ v i := fun i => (hy i).trans (hyv i)
  calc ns y ≤ ns v := norm_mono_abs ns hns y v (fun i => by
         simpa [abs_of_nonneg (hy i), abs_of_nonneg (hv i)] using hyv i)
    _ ≤ ns u := lemma_3_1 ns hns.toIsPermInvNorm u v huv

lemma hull_of_weak {n : ℕ} (ns : (Fin n → ℝ) → ℝ) (hns : IsSymmetricGauge ns)
    (K : ℕ) (u x : Fin n → ℝ) (hu : u ∈ NK ns K) (h : WeakMajorizes u (absVec x)) :
    x ∈ convexHull ℝ (NK ns K) := by
  obtain ⟨v, huv, hxv⟩ := weak_majorization_5A9 u (absVec x) h
  have hv : ∀ i, 0 ≤ v i := fun i => (abs_nonneg (x i)).trans (hxv i)
  have hperm : permHull u ⊆ convexHull ℝ (NK ns K) := by
    apply convexHull_min
    · rintro _ ⟨σ, rfl⟩
      apply subset_convexHull ℝ (NK ns K)
      change ns (u ∘ σ) ≤ 1 ∧ card (u ∘ σ) ≤ K
      rw [hns.perm, card_perm]
      exact hu
    · exact convex_convexHull ℝ _
  have hvmem : v ∈ permHull u := by rw [majorization_principle]; exact huv
  apply hull_mono_abs ns hns K x v ?_ (hperm hvmem)
  intro i
  simpa [absVec, abs_of_nonneg (hv i)] using hxv i

lemma feas_nonneg {n : ℕ} {K : ℕ} {x u : Fin n → ℝ} (hu : u ∈ Feas11 K x) :
    ∀ i, 0 ≤ u i := by
  intro i
  by_cases hi : (i : ℕ) < K
  · exact hu.2.1 i hi
  · rw [hu.2.2.1 i (by omega)]

lemma feas_antitone {n : ℕ} {K : ℕ} {x u : Fin n → ℝ} (hu : u ∈ Feas11 K x) :
    Antitone u := by
  intro i j hij
  by_cases hj : (j : ℕ) < K
  · exact hu.1 i j hij hj
  · rw [hu.2.2.1 j (by omega)]
    exact feas_nonneg hu i

lemma feas_card {n : ℕ} (K : ℕ) (hKn : K ≤ n) (x u : Fin n → ℝ)
    (hu : u ∈ Feas11 K x) : card u ≤ K := by
  classical
  unfold card
  calc
    (Finset.univ.filter (fun i => u i ≠ 0)).card ≤
        (Finset.univ.filter (fun i : Fin n => (i : ℕ) < K)).card := by
      apply Finset.card_le_card
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
      by_contra! hn
      exact hi (hu.2.2.1 i hn)
    _ = K := main_card_R K hKn

lemma largest_sorted {n : ℕ} (u : Fin n → ℝ) (hu : Antitone u) (j : ℕ) (hj : j ≤ n) :
    sumLargest j u = ∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < j), u i := by
  apply le_antisymm
  · simpa using main_sumLargest_le u (Equiv.refl _) hu j hj
  · exact main_le_sumLargest u _ j (main_card_R j hj)

lemma largest_abs_mix {n : ℕ} (x y : Fin n → ℝ) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (j : ℕ) (hj : j ≤ n) :
    sumLargest j (absVec (a • x + b • y)) ≤ a * sumLargest j (absVec x) + b * sumLargest j (absVec y) := by
  classical
  unfold sumLargest
  have : Nonempty {s : Finset (Fin n) // s.card = j} := ⟨⟨_, main_card_R j hj⟩⟩
  apply ciSup_le
  intro s
  change (∑ i ∈ s.1, |a * x i + b * y i|) ≤ _
  calc
    (∑ i ∈ s.1, |a * x i + b * y i|) ≤ ∑ i ∈ s.1, (a * |x i| + b * |y i|) := by
      apply Finset.sum_le_sum
      intro i hi
      simpa [abs_mul, abs_of_nonneg ha, abs_of_nonneg hb] using abs_add_le (a * x i) (b * y i)
    _ = a * ∑ i ∈ s.1, |x i| + b * ∑ i ∈ s.1, |y i| := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ _ := add_le_add
      (mul_le_mul_of_nonneg_left (main_le_sumLargest (absVec x) s.1 j s.2) ha)
      (mul_le_mul_of_nonneg_left (main_le_sumLargest (absVec y) s.1 j s.2) hb)

lemma feas_mix {n : ℕ} (K : ℕ) (x y u v : Fin n → ℝ)
    (hu : u ∈ Feas11 K x) (hv : v ∈ Feas11 K y) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a • u + b • v ∈ Feas11 K (a • x + b • y) := by
  classical
  have hsorted : Antitone (a • u + b • v) := by
    intro i j hij
    exact add_le_add (mul_le_mul_of_nonneg_left (feas_antitone hu hij) ha)
      (mul_le_mul_of_nonneg_left (feas_antitone hv hij) hb)
  refine ⟨fun i j hij _ => hsorted hij, ?_, ?_, ?_⟩
  · intro i hi
    exact add_nonneg (mul_nonneg ha (hu.2.1 i hi)) (mul_nonneg hb (hv.2.1 i hi))
  · intro i hi
    change a * u i + b * v i = 0
    rw [hu.2.2.1 i hi, hv.2.2.1 i hi]
    ring
  · intro j hj1 hjn
    calc
      sumLargest j (absVec (a • x + b • y)) ≤
          a * sumLargest j (absVec x) + b * sumLargest j (absVec y) :=
        largest_abs_mix x y a b ha hb j hjn
      _ ≤ a * sumLargest j u + b * sumLargest j v := add_le_add
        (mul_le_mul_of_nonneg_left (hu.2.2.2 j hj1 hjn) ha)
        (mul_le_mul_of_nonneg_left (hv.2.2.2 j hj1 hjn) hb)
      _ = sumLargest j (a • u + b • v) := by
        rw [largest_sorted u (feas_antitone hu) j hjn,
          largest_sorted v (feas_antitone hv) j hjn, largest_sorted _ hsorted j hjn]
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib, ← Finset.mul_sum]

lemma feasible_sublevel_convex {n : ℕ} (ns : (Fin n → ℝ) → ℝ) (hns : IsPermInvNorm ns) (K : ℕ) :
    Convex ℝ {x | ∃ u ∈ Feas11 K x, ns u ≤ 1} := by
  intro x hx y hy a b ha hb hab
  obtain ⟨u, hu, hnu⟩ := hx
  obtain ⟨v, hv, hnv⟩ := hy
  exact ⟨a • u + b • v, feas_mix K x y u v hu hv a b ha hb,
    norm_sublevel ns hns 1 hnu hnv ha hb hab⟩

noncomputable def decPerm {n : ℕ} (x : Fin n → ℝ) : Equiv.Perm (Fin n) :=
  Fin.revPerm.trans (Tuple.sort (absVec x))

lemma dec_eq {n : ℕ} (x : Fin n → ℝ) : decAbs x = absVec x ∘ decPerm x := rfl

lemma dec_antitone {n : ℕ} (x : Fin n → ℝ) : Antitone (decAbs x) := by
  intro i j hij
  exact Tuple.monotone_sort (absVec x) (Fin.rev_le_rev.mpr hij)

lemma card_abs {n : ℕ} (x : Fin n → ℝ) : card (absVec x) = card x := by
  simp [card, absVec]

lemma card_dec {n : ℕ} (x : Fin n → ℝ) : card (decAbs x) = card x := by
  rw [dec_eq, card_perm, card_abs]

lemma largest_perm_eq {n : ℕ} (x : Fin n → ℝ) (σ : Equiv.Perm (Fin n)) (j : ℕ) (hj : j ≤ n) :
    sumLargest j (x ∘ σ) = sumLargest j x := by
  apply le_antisymm (main_sumLargest_perm x σ j hj)
  simpa [Function.comp_def] using main_sumLargest_perm (x ∘ σ) σ.symm j hj

lemma dec_feasible {n : ℕ} (K : ℕ) (x : Fin n → ℝ) (hx : card x ≤ K) :
    decAbs x ∈ Feas11 K x := by
  classical
  refine ⟨fun i j hij _ => dec_antitone x hij, fun i _ => abs_nonneg _, ?_, ?_⟩
  · intro i hi
    by_contra hne
    have hp : 0 < decAbs x i := lt_of_le_of_ne (abs_nonneg _) (Ne.symm hne)
    have hcount : i.val + 1 ≤ card (decAbs x) := by
      rw [← main_card_R (m := n) (i.val + 1) (by omega)]
      apply Finset.card_le_card
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
      exact ne_of_gt (hp.trans_le (dec_antitone x (Fin.le_iff_val_le_val.mpr (by omega))))
    rw [card_dec] at hcount
    omega
  · intro j hj1 hjn
    rw [dec_eq, largest_perm_eq _ _ j hjn]

lemma norm_dec {n : ℕ} (ns : (Fin n → ℝ) → ℝ) (hns : IsSymmetricGauge ns) (x : Fin n → ℝ) :
    ns (decAbs x) = ns x := by
  rw [dec_eq, hns.perm]
  exact hns.sign _ _ (fun i => by simp [absVec])

lemma hull_iff_feasible {n : ℕ} (ns : (Fin n → ℝ) → ℝ) (hns : IsSymmetricGauge ns)
    (K : ℕ) (hKn : K ≤ n) (x : Fin n → ℝ) :
    x ∈ convexHull ℝ (NK ns K) ↔ ∃ u ∈ Feas11 K x, ns u ≤ 1 := by
  constructor
  · apply convexHull_min ?_ (feasible_sublevel_convex ns hns.toIsPermInvNorm K)
    intro z hz
    refine ⟨decAbs z, dec_feasible K z hz.2, ?_⟩
    rw [norm_dec ns hns]
    exact hz.1
  · rintro ⟨u, hu, hnu⟩
    exact hull_of_weak ns hns K u x ⟨hnu, feas_card K hKn x u hu⟩ hu.2.2.2

end MainAux


open PermInvConvex.Sparsity ModernConvex.Spectral

namespace MainAux

noncomputable def pref {n : ℕ} (u : Fin n → ℝ) (j : ℕ) : ℝ :=
  ∑ k ∈ Finset.range j, main_ext u k

lemma pref_largest {n : ℕ} (u : Fin n → ℝ) (hu : Antitone u) (j : ℕ) (hj : j ≤ n) :
    pref u j = sumLargest j u := by
  rw [largest_sorted u hu j hj, pref, main_sum_ext u j hj]

lemma sorted_chord {n : ℕ} (u : Fin n → ℝ) (hu : Antitone u)
    (s j K : ℕ) (hsj : s ≤ j) (hjK : j ≤ K) (hKn : K ≤ n) :
    ((K - j : ℕ) : ℝ) * pref u s + ((j - s : ℕ) : ℝ) * pref u K ≤
      ((K - s : ℕ) : ℝ) * pref u j := by
  classical
  have hcmp : ∀ p ∈ Finset.Ico s j, ∀ q ∈ Finset.Ico j K,
      main_ext u q ≤ main_ext u p := by
    intro p hp q hq
    simp only [Finset.mem_Ico] at hp hq
    simp only [main_ext, dif_pos (show q < n by omega), dif_pos (show p < n by omega)]
    exact hu (Fin.le_iff_val_le_val.mpr (by change p ≤ q; omega))
  have hc := Finset.sum_le_sum (s := Finset.Ico s j) (fun p hp =>
    Finset.sum_le_sum (s := Finset.Ico j K) (fun q hq => hcmp p hp q hq))
  simp only [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, ← Finset.mul_sum] at hc
  have hmid : ∑ p ∈ Finset.Ico s j, main_ext u p = pref u j - pref u s :=
    Finset.sum_Ico_eq_sub _ hsj
  rw [hmid] at hc
  have hkj : ((K - j : ℕ) : ℝ) = K - j := by rw [Nat.cast_sub hjK]
  have hjs : ((j - s : ℕ) : ℝ) = j - s := by rw [Nat.cast_sub hsj]
  have hks : ((K - s : ℕ) : ℝ) = K - s := by rw [Nat.cast_sub (hsj.trans hjK)]
  have htail : ∑ q ∈ Finset.Ico j K, main_ext u q = pref u K - pref u j :=
    Finset.sum_Ico_eq_sub _ hjK
  rw [htail, hkj, hjs] at hc
  rw [hkj, hjs, hks]
  nlinarith

lemma pref_supported {n : ℕ} (u : Fin n → ℝ) (K : ℕ)
    (hsupport : ∀ i, K ≤ i.val → u i = 0) (j : ℕ) (hKj : K ≤ j) (hjn : j ≤ n) :
    pref u j = ∑ i, u i := by
  classical
  rw [pref, main_sum_ext u j hjn]
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro i hi hnot
  apply hsupport
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hnot
  omega

lemma pref_plateau {n : ℕ} (w : Fin n → ℝ) (s K : ℕ) (hKn : K ≤ n) (d : ℝ)
    (hplateau : ∀ i, s ≤ i.val → i.val < K → w i = d)
    (j : ℕ) (hsj : s ≤ j) (hjK : j ≤ K) :
    pref w j = pref w s + ((j - s : ℕ) : ℝ) * d := by
  classical
  have he : ∑ k ∈ Finset.Ico s j, main_ext w k = ((j - s : ℕ) : ℝ) * d := by
    calc
      _ = ∑ k ∈ Finset.Ico s j, d := by
        apply Finset.sum_congr rfl
        intro k hk
        simp only [Finset.mem_Ico] at hk
        simp only [main_ext, dif_pos (show k < n by omega)]
        exact hplateau ⟨k, by omega⟩ hk.1 (by change k < K; omega)
      _ = _ := by simp
  have ht := Finset.sum_range_add_sum_Ico (main_ext w) hsj
  change pref w s + _ = pref w j at ht
  rw [he] at ht
  exact ht.symm

lemma head_plateau_weak_min {n : ℕ} (K s : ℕ) (hsK : s < K) (hKn : K ≤ n)
    (x w u : Fin n → ℝ) (d : ℝ) (hwsorted : Antitone w)
    (hhead : ∀ i, i.val < s → w i = decAbs x i)
    (hplateau : ∀ i, s ≤ i.val → i.val < K → w i = d)
    (hsupport : ∀ i, K ≤ i.val → w i = 0)
    (htotal : ∑ i, w i = ∑ i, absVec x i) (hu : u ∈ Feas11 K x) :
    WeakMajorizes u w := by
  classical
  have husorted := feas_antitone hu
  have hu_support : ∀ i, K ≤ i.val → u i = 0 := hu.2.2.1
  have hheadBound : ∀ j, j ≤ s → pref w j ≤ pref u j := by
    intro j hjs
    by_cases hj0 : j = 0
    · subst j; simp [pref]
    have hjn : j ≤ n := hjs.trans (hsK.le.trans hKn)
    have he : pref w j = pref (decAbs x) j := by
      unfold pref
      apply Finset.sum_congr rfl
      intro k hk
      have hkj := Finset.mem_range.mp hk
      simp only [main_ext, dif_pos (show k < n by omega)]
      exact hhead ⟨k, by omega⟩ (by change k < s; omega)
    rw [he, pref_largest _ (dec_antitone x) j hjn,
      pref_largest _ husorted j hjn, dec_eq, largest_perm_eq _ _ j hjn]
    exact hu.2.2.2 j (by omega) hjn
  have htotalBound : ∑ i, w i ≤ ∑ i, u i := by
    rw [htotal]
    calc
      _ ≤ sumLargest n (absVec x) := main_le_sumLargest _ Finset.univ n (by simp)
      _ ≤ sumLargest n u := hu.2.2.2 n (by omega) le_rfl
      _ = ∑ i, u i := by
        rw [← pref_largest u husorted n le_rfl,
          pref_supported u K hu_support n hKn le_rfl]
  have hKBound : pref w K ≤ pref u K := by
    rw [pref_supported w K hsupport K le_rfl hKn,
      pref_supported u K hu_support K le_rfl hKn]
    exact htotalBound
  intro j hj1 hjn
  rw [← pref_largest w hwsorted j hjn, ← pref_largest u husorted j hjn]
  by_cases hjs : j ≤ s
  · exact hheadBound j hjs
  by_cases hKj : K ≤ j
  · rw [pref_supported w K hsupport j hKj hjn,
      pref_supported u K hu_support j hKj hjn]
    exact htotalBound
  have hsj : s ≤ j := by omega
  have hjK : j ≤ K := by omega
  have hc := sorted_chord u husorted s j K hsj hjK hKn
  have hb1 := mul_le_mul_of_nonneg_left (hheadBound s le_rfl)
    (show (0 : ℝ) ≤ ((K - j : ℕ) : ℝ) by positivity)
  have hb2 := mul_le_mul_of_nonneg_left hKBound
    (show (0 : ℝ) ≤ ((j - s : ℕ) : ℝ) by positivity)
  have hpj := pref_plateau w s K hKn d hplateau j hsj hjK
  have hpK := pref_plateau w s K hKn d hplateau K hsK.le le_rfl
  have hkj : ((K - j : ℕ) : ℝ) = K - j := by rw [Nat.cast_sub hjK]
  have hjs : ((j - s : ℕ) : ℝ) = j - s := by rw [Nat.cast_sub hsj]
  have hks : ((K - s : ℕ) : ℝ) = K - s := by rw [Nat.cast_sub hsK.le]
  have hpos : (0 : ℝ) < ((K - s : ℕ) : ℝ) := by exact_mod_cast Nat.sub_pos_of_lt hsK
  have hmul : ((K - s : ℕ) : ℝ) * pref w j ≤ ((K - s : ℕ) : ℝ) * pref u j := by
    calc
      _ = ((K - j : ℕ) : ℝ) * pref w s + ((j - s : ℕ) : ℝ) * pref w K := by
        rw [hpj, hpK]
        simp only [hkj, hjs, hks]
        ring
      _ ≤ _ := (add_le_add hb1 hb2).trans hc
  exact (mul_le_mul_iff_right₀ hpos).mp hmul

end MainAux


open PermInvConvex.Sparsity ModernConvex.Spectral

namespace MainAux

lemma largest_total {n : ℕ} (x : Fin n → ℝ) : sumLargest n x = ∑ i, x i := by
  classical
  apply le_antisymm
  · unfold sumLargest
    have : Nonempty {s : Finset (Fin n) // s.card = n} := ⟨⟨Finset.univ, by simp⟩⟩
    apply ciSup_le
    intro s
    have hs : s.1 = Finset.univ := by
      apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
      simp [s.2]
    rw [hs]
  · exact main_le_sumLargest x Finset.univ n (by simp)

lemma majorizes_weak {n : ℕ} (u x : Fin n → ℝ) (h : Majorizes u x) : WeakMajorizes u x := by
  intro j hj1 hjn
  by_cases hj : j = n
  · subst j
    rw [largest_total, largest_total, h.2]
  · exact h.1 j hj1 (by omega)

/- The following explicit-index lemmas adapt the proofs in the accepted
proposition_3_4 source. Registered recurrence and unimodality clauses are used
through the theorem statement; all other helper proofs are included locally. -/
lemma ix_bounds {n : ℕ} (K : ℕ) (hK : 1 ≤ K) (x : Fin n → ℝ) :
    1 ≤ ix K x ∧ ix K x ≤ K ∧
      ∀ i : ℕ, 1 ≤ i → i ≤ K → sVal K x (ix K x) ≤ sVal K x i := by
  have hne : {i : ℕ | 1 ≤ i ∧ i ≤ K ∧
      ∀ j : ℕ, 1 ≤ j → j ≤ K → sVal K x i ≤ sVal K x j}.Nonempty := by
    obtain ⟨i, hi, hmin⟩ := Finset.exists_min_image (Finset.Icc 1 K) (sVal K x)
      ⟨1, by simp [hK]⟩
    refine ⟨i, (Finset.mem_Icc.mp hi).1, (Finset.mem_Icc.mp hi).2, ?_⟩
    intro j hj hjK
    exact hmin j (Finset.mem_Icc.mpr ⟨hj, hjK⟩)
  exact csInf_mem hne

lemma delta_nonneg {n : ℕ} (K : ℕ) (hK : 1 < K) (x : Fin n → ℝ) : 0 ≤ delta K x := by
  obtain ⟨hm1, hmK, _⟩ := ix_bounds K hK.le x
  unfold delta sVal
  apply div_nonneg
  · exact Finset.sum_nonneg (fun i _ => abs_nonneg _)
  · have hm : (ix K x : ℝ) ≤ K := by exact_mod_cast hmK
    linarith

lemma delta_head {n : ℕ} (K : ℕ) (hK : 1 < K) (hKn : K < n) (x : Fin n → ℝ)
    (j : Fin n) (hj : (j : ℕ) + 1 < ix K x) : delta K x ≤ decAbs x j := by
  obtain ⟨hm1, hmK, hmin⟩ := ix_bounds K hK.le x
  have hth := proposition_3_4 K hK hKn x
  have hr := (hth.1 ((j : ℕ) + 1) (by omega) (by omega)).1
  have hdec := hth.2.1.1 ((j : ℕ) + 1) ((j : ℕ) + 1 + 1)
    (by omega) (by omega) (by omega)
  have hd : 0 < 1 / ((K : ℝ) - ((j : ℕ) + 1) + 1) := by
    apply one_div_pos.mpr
    have hcast : (((j : ℕ) + 1 : ℕ) : ℝ) ≤ K := by exact_mod_cast (show (j : ℕ) + 1 ≤ K by omega)
    push_cast at hcast
    linarith
  have hp : 1 / ((K : ℝ) - ((j : ℕ) + 1) + 1) *
      (sVal K x ((j : ℕ) + 1 + 1) - decAbs x j) ≤ 0 := by
    simpa only [Nat.add_sub_cancel, Fin.eta, Nat.cast_add, Nat.cast_one] using hr.symm.trans_le (sub_nonpos.mpr hdec)
  exact (hmin ((j : ℕ) + 1 + 1) (by omega) (by omega)).trans
    (by nlinarith)

lemma u_nonneg {n : ℕ} (K : ℕ) (hK : 1 < K) (x : Fin n → ℝ) (j : Fin n) :
    0 ≤ uVec K x j := by
  unfold uVec
  split_ifs
  · exact abs_nonneg _
  · exact delta_nonneg K hK x
  · exact le_rfl

lemma u_antitone {n : ℕ} (K : ℕ) (hK : 1 < K) (hKn : K < n) (x : Fin n → ℝ) :
    Antitone (uVec K x) := by
  obtain ⟨hm1, hmK, _⟩ := ix_bounds K hK.le x
  intro i j hij
  have hij' : (i : ℕ) ≤ (j : ℕ) := hij
  unfold uVec
  split_ifs with hjm hjK him hiK
  all_goals first
  | exact dec_antitone x hij
  | exact delta_head K hK hKn x i (by omega)
  | exact abs_nonneg _
  | exact delta_nonneg K hK x
  | exact le_rfl
  | omega

lemma u_support {n : ℕ} (K : ℕ) (hK : 1 < K) (x : Fin n → ℝ)
    (i : Fin n) (hi : K ≤ i.val) : uVec K x i = 0 := by
  obtain ⟨hm1, hmK, _⟩ := ix_bounds K hK.le x
  simp [uVec, show ¬i.val + 1 < ix K x by omega, show ¬i.val + 1 ≤ K by omega]

lemma u_feasible {n : ℕ} (K : ℕ) (hK : 1 < K) (hKn : K < n) (x : Fin n → ℝ) :
    uVec K x ∈ Feas11 K x := by
  refine ⟨fun i j hij _ => u_antitone K hK hKn x hij,
    fun i _ => u_nonneg K hK x i, u_support K hK x, ?_⟩
  exact majorizes_weak _ _ (proposition_3_4 K hK hKn x).2.2.1

lemma u_weak_min {n : ℕ} (K : ℕ) (hK : 1 < K) (hKn : K < n) (x u : Fin n → ℝ)
    (hu : u ∈ Feas11 K x) : WeakMajorizes u (uVec K x) := by
  obtain ⟨hm1, hmK, _⟩ := ix_bounds K hK.le x
  apply head_plateau_weak_min K (ix K x - 1) (by omega) hKn.le x (uVec K x) u
    (delta K x) (u_antitone K hK hKn x)
  · intro i hi
    simp [uVec, show i.val + 1 < ix K x by omega]
  · intro i hi hiK
    simp [uVec, show ¬i.val + 1 < ix K x by omega, show i.val + 1 ≤ K by omega]
  · exact u_support K hK x
  · exact (proposition_3_4 K hK hKn x).2.2.1.2.symm
  · exact hu

end MainAux

open MainAux

theorem solution {n : ℕ} (ns : (Fin n → ℝ) → ℝ) (hns : IsSymmetricGauge ns)
    (K : ℕ) (hK : 1 < K) (hKn : K < n) (x : Fin n → ℝ) :
    (uVec K x ∈ Feas11 K x ∧ ∀ u ∈ Feas11 K x, ns (uVec K x) ≤ ns u) ∧
    (x ∈ convexHull ℝ (NK ns K) ↔ ns (uVec K x) ≤ 1) := by
  have hf := u_feasible K hK hKn x
  have hmin : ∀ u ∈ Feas11 K x, ns (uVec K x) ≤ ns u := by
    intro u hu
    exact norm_weak_mono ns hns u (uVec K x) (u_nonneg K hK x) (u_weak_min K hK hKn x u hu)
  refine ⟨⟨hf, hmin⟩, ?_⟩
  rw [hull_iff_feasible ns hns K hKn.le x]
  constructor
  · rintro ⟨u, hu, hnu⟩
    exact (hmin u hu).trans hnu
  · intro hn
    exact ⟨uVec K x, hf, hn⟩
