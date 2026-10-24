-- Prove2me | solution 1 for PermInvConvex.Sparsity.weak_majorization_5A9
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T06:12:09.080195+00:00
-- url     : https://prove2.me/submissions/0fcd942c-cc15-48b5-bfd1-93b9c1dffebb

import Mathlib
import Definitions.Def_ModernConvex_Spectral_SDR
import Definitions.Def_PermInvConvex_Sparsity_Majorization
import Definitions.Def_PermInvConvex_Sparsity_Setting

open Matrix
open ModernConvex.Spectral
open PermInvConvex.Sparsity
open scoped Pointwise

/- The elementary sorting and Abel-summation helper proofs below are adapted
from the accepted majorization-principle proof (external proved ID
09334e4e-60b2-4847-9e47-653ee5c5d8af; submission
13309f84-3eaf-45da-a5b5-d6dcbb7d3b72). They are checked in this file; no
external theorem or target theorem is imported. -/

lemma wm5a9_abel (b c w : ℕ → ℝ) (n : ℕ) (hb : ∀ k, k + 1 < n → b (k + 1) ≤ b k)
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
noncomputable def wm5a9_ext {m : ℕ} (g : Fin m → ℝ) (k : ℕ) : ℝ :=
  if h : k < m then g ⟨k, h⟩ else 0

lemma wm5a9_ext_val {m : ℕ} (g : Fin m → ℝ) (i : Fin m) : wm5a9_ext g i = g i := by
  simp [wm5a9_ext, i.2]

lemma wm5a9_sum_ext {m : ℕ} (g : Fin m → ℝ) (j : ℕ) (hj : j ≤ m) :
    ∑ k ∈ Finset.range j, wm5a9_ext g k =
      ∑ i ∈ Finset.univ.filter (fun i : Fin m => (i : ℕ) < j), g i := by
  rw [Finset.sum_filter]
  have h1 : ∑ i : Fin m, (if (i : ℕ) < j then g i else 0) =
      ∑ i : Fin m, (fun k : ℕ => if k < j then wm5a9_ext g k else 0) (i : ℕ) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [wm5a9_ext_val]
  rw [h1, Fin.sum_univ_eq_sum_range (fun k : ℕ => if k < j then wm5a9_ext g k else 0) m,
    ← Finset.sum_filter]
  congr 1
  ext k
  simp only [Finset.mem_range, Finset.mem_filter]
  omega

lemma wm5a9_card_R {m : ℕ} (j : ℕ) (hj : j ≤ m) :
    (Finset.univ.filter (fun i : Fin m => (i : ℕ) < j)).card = j := by
  rw [Fin.card_filter_val_lt]; omega

lemma wm5a9_top {m : ℕ} (c : Fin m → ℝ) (hc : Antitone c) (s : Finset (Fin m)) (j : ℕ)
    (hs : s.card = j) :
    ∑ i ∈ s, c i ≤ ∑ i ∈ Finset.univ.filter (fun i : Fin m => (i : ℕ) < j), c i := by
  set R := Finset.univ.filter (fun i : Fin m => (i : ℕ) < j) with hR
  have hjm : j ≤ m := by rw [← hs]; simpa using Finset.card_le_univ s
  have hRc : R.card = j := wm5a9_card_R j hjm
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

lemma wm5a9_le_sumLargest {m : ℕ} (y : Fin m → ℝ) (s : Finset (Fin m)) (j : ℕ) (hs : s.card = j) :
    ∑ i ∈ s, y i ≤ sumLargest j y := by
  unfold sumLargest
  exact le_ciSup (f := fun s : {s : Finset (Fin m) // s.card = j} => ∑ i ∈ s.1, y i)
    (Set.finite_range _).bddAbove ⟨s, hs⟩

lemma wm5a9_sumLargest_le {m : ℕ} (x : Fin m → ℝ) (π : Equiv.Perm (Fin m)) (hπ : Antitone (x ∘ π))
    (j : ℕ) (hj : j ≤ m) :
    sumLargest j x ≤ ∑ k ∈ Finset.univ.filter (fun i : Fin m => (i : ℕ) < j), x (π k) := by
  unfold sumLargest
  have : Nonempty {s : Finset (Fin m) // s.card = j} :=
    ⟨⟨_, wm5a9_card_R j hj⟩⟩
  refine ciSup_le fun s => ?_
  have hc : (s.1.map π.symm.toEmbedding).card = j := by rw [Finset.card_map]; exact s.2
  have := wm5a9_top (x ∘ π) hπ _ j hc
  simpa [Finset.sum_map] using this

lemma wm5a9_sumLargest_perm {m : ℕ} (x : Fin m → ℝ) (σ : Equiv.Perm (Fin m)) (j : ℕ) (hj : j ≤ m) :
    sumLargest j (x ∘ σ) ≤ sumLargest j x := by
  conv_lhs => unfold sumLargest
  have : Nonempty {s : Finset (Fin m) // s.card = j} :=
    ⟨⟨_, wm5a9_card_R j hj⟩⟩
  refine ciSup_le fun s => ?_
  have hc : (s.1.map σ.toEmbedding).card = j := by rw [Finset.card_map]; exact s.2
  have := wm5a9_le_sumLargest x _ j hc
  simpa [Finset.sum_map] using this

lemma wm5a9_sumLargest_convex {m : ℕ} (j : ℕ) (hj : j ≤ m) (y y' : Fin m → ℝ) (a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    sumLargest j (a • y + b • y') ≤ a * sumLargest j y + b * sumLargest j y' := by
  conv_lhs => unfold sumLargest
  have : Nonempty {s : Finset (Fin m) // s.card = j} :=
    ⟨⟨_, wm5a9_card_R j hj⟩⟩
  refine ciSup_le fun s => ?_
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib, ← Finset.mul_sum]
  have h1 := wm5a9_le_sumLargest y s.1 j s.2
  have h2 := wm5a9_le_sumLargest y' s.1 j s.2
  nlinarith

lemma wm5a9_antitone_sort {m : ℕ} (x : Fin m → ℝ) : Antitone (x ∘ Tuple.sort (fun i => -x i)) := by
  intro i k hik
  have := Tuple.monotone_sort (fun i => -x i) hik
  simp only [Function.comp_apply] at this ⊢
  linarith

lemma wm5a9_hull_majorizes {n : ℕ} (u : Fin n → ℝ) :
    permHull u ⊆ {z | Majorizes u z} := by
  refine convexHull_min ?_ ?_
  · rintro _ ⟨σ, rfl⟩
    refine ⟨fun j _ hj => wm5a9_sumLargest_perm u σ j (by omega), ?_⟩
    exact Equiv.sum_comp σ u
  · intro y hy y' hy' a b ha hb hab
    refine ⟨fun j hj1 hj2 => ?_, ?_⟩
    · calc sumLargest j (a • y + b • y') ≤ a * sumLargest j y + b * sumLargest j y' :=
            wm5a9_sumLargest_convex j (by omega) y y' a b ha hb
        _ ≤ a * sumLargest j u + b * sumLargest j u := by
            have := hy.1 j hj1 hj2; have := hy'.1 j hj1 hj2; nlinarith
        _ = sumLargest j u := by rw [← add_mul, hab, one_mul]
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
        ← Finset.mul_sum, hy.2, hy'.2]
      rw [← add_mul, hab, one_mul]

/-- Weak majorization controls every nonnegative linear functional by a permutation. -/
lemma wm5a9_nonnegative_support {n : ℕ} (u y a : Fin n → ℝ)
    (h : WeakMajorizes u y) (ha : ∀ i, 0 ≤ a i) :
    ∃ σ : Equiv.Perm (Fin n), ∑ i, y i * a i ≤ ∑ i, u (σ i) * a i := by
  classical
  set τ := Tuple.sort (fun i => -a i) with hτ
  set π := Tuple.sort (fun i => -u i) with hπ
  have hτa : Antitone (a ∘ τ) := wm5a9_antitone_sort a
  have hπu : Antitone (u ∘ π) := wm5a9_antitone_sort u
  refine ⟨τ.symm.trans π, ?_⟩
  rw [← Equiv.sum_comp τ (fun i => y i * a i),
    ← Equiv.sum_comp τ (fun i => u ((τ.symm.trans π) i) * a i)]
  simp only [Equiv.trans_apply, Equiv.symm_apply_apply]
  set b := wm5a9_ext (a ∘ τ)
  set c := wm5a9_ext (u ∘ π)
  set w := wm5a9_ext (y ∘ τ)
  have hb : ∀ k, k + 1 < n → b (k + 1) ≤ b k := by
    intro k hk
    simp only [b, wm5a9_ext, dif_pos hk, dif_pos (show k < n by omega)]
    exact hτa (Fin.le_iff_val_le_val.mpr (by simp))
  have hbn : 0 ≤ b (n - 1) := by
    dsimp [b, wm5a9_ext]
    split
    · exact ha _
    · exact le_rfl
  have hpart : ∀ j, j ≤ n → ∑ k ∈ Finset.range j, (c k - w k) =
      ∑ k ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < j), u (π k) -
      ∑ i ∈ (Finset.univ.filter (fun i : Fin n => (i : ℕ) < j)).map τ.toEmbedding, y i := by
    intro j hj
    rw [Finset.sum_sub_distrib, wm5a9_sum_ext _ j hj, wm5a9_sum_ext _ j hj,
      Finset.sum_map]
    rfl
  have hD : ∀ j, j ≤ n → 0 ≤ ∑ k ∈ Finset.range j, (c k - w k) := by
    intro j hj
    rcases Nat.eq_zero_or_pos j with h0 | hpos
    · subst h0; simp
    rw [hpart j hj, sub_nonneg]
    have hc : ((Finset.univ.filter (fun i : Fin n => (i : ℕ) < j)).map τ.toEmbedding).card = j := by
      rw [Finset.card_map, wm5a9_card_R j hj]
    calc _ ≤ sumLargest j y := wm5a9_le_sumLargest y _ j hc
      _ ≤ sumLargest j u := h j hpos hj
      _ ≤ _ := wm5a9_sumLargest_le u π hπu j hj
  have habel := wm5a9_abel b c w n hb (fun j hj => hD j hj.le)
  have hnonneg := (mul_nonneg hbn (hD n le_rfl)).trans habel
  have hconv : ∑ k ∈ Finset.range n, b k * (c k - w k) =
      ∑ k : Fin n, a (τ k) * (u (π k) - y (τ k)) := by
    rw [← Fin.sum_univ_eq_sum_range (fun k => b k * (c k - w k)) n]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [b, c, w, wm5a9_ext_val, Function.comp_apply]
  rw [hconv] at hnonneg
  have : 0 ≤ ∑ k : Fin n, (u (π k) * a (τ k) - y (τ k) * a (τ k)) := by
    refine hnonneg.trans_eq (Finset.sum_congr rfl fun k _ => by ring)
  rw [Finset.sum_sub_distrib] at this
  linarith

/-- The original registered target, with all of its original binders. -/
theorem solution {n : ℕ} (u y : Fin n → ℝ) (h : WeakMajorizes u y) :
    ∃ u' : Fin n → ℝ, Majorizes u u' ∧ y ≤ u' := by
  classical
  let C : Set (Fin n → ℝ) := permHull u + Set.Iic 0
  have hu : u ∈ permHull u := subset_convexHull ℝ _ ⟨Equiv.refl _, rfl⟩
  have hull_sub : permHull u ⊆ C := by
    intro v hv
    exact Set.mem_add.mpr ⟨v, hv, 0, by simp, add_zero v⟩
  have hC : Convex ℝ C := (convex_convexHull ℝ _).add (convex_Iic 0)
  have hclosed : IsClosed C := isClosed_Iic.add_left_of_isCompact
    ((Set.finite_range (fun σ : Equiv.Perm (Fin n) => u ∘ σ)).isCompact_convexHull ℝ)
  have hyC : y ∈ C := by
    by_contra hy
    obtain ⟨f, r, hfr, hry⟩ := geometric_hahn_banach_closed_point hC hclosed hy
    let a : Fin n → ℝ := fun i => f (fun j => if i = j then 1 else 0)
    have hf : ∀ v : Fin n → ℝ, f v = ∑ i, v i * a i := by
      intro v
      have := LinearMap.pi_apply_eq_sum_univ (f : (Fin n → ℝ) →ₗ[ℝ] ℝ) v
      simpa [a, smul_eq_mul] using this
    have ha : ∀ i, 0 ≤ a i := by
      intro i
      by_contra! hai
      let t : ℝ := (r - f u + 1) / a i
      have hfu := hfr u (hull_sub hu)
      have ht : t ≤ 0 := div_nonpos_of_nonneg_of_nonpos (by linarith) hai.le
      let e : Fin n → ℝ := fun j => if i = j then 1 else 0
      have he : t • e ∈ Set.Iic (0 : Fin n → ℝ) := by
        intro j
        dsimp [e]
        split_ifs
        · simpa using ht
        · simp
      have hv : u + t • e ∈ C := Set.mem_add.mpr ⟨u, hu, t • e, he, rfl⟩
      have hvf := hfr _ hv
      rw [map_add, map_smul, smul_eq_mul] at hvf
      have heq : f e = a i := rfl
      rw [heq, show t * a i = r - f u + 1 from div_mul_cancel₀ _ (ne_of_lt hai)] at hvf
      linarith
    obtain ⟨σ, hσ⟩ := wm5a9_nonnegative_support u y a h ha
    have hmem : u ∘ σ ∈ C := hull_sub (subset_convexHull ℝ _ ⟨σ, rfl⟩)
    have := hfr _ hmem
    rw [hf] at this hry
    dsimp [Function.comp] at this
    linarith
  obtain ⟨u', hu', v, hv, huv⟩ := Set.mem_add.mp hyC
  refine ⟨u', wm5a9_hull_majorizes u hu', ?_⟩
  rw [← huv]
  exact add_le_of_nonpos_right hv
