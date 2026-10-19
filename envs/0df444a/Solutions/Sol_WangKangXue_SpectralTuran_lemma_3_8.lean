-- Prove2me | solution 1 for WangKangXue.SpectralTuran.lemma_3_8
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-17T13:16:25.239188+00:00
-- url     : https://prove2.me/submissions/9fa09066-58e2-4626-9e92-dd698161e93e

import Mathlib
import Definitions.Def_WangKangXue_SpectralTuran_specRad
import Definitions.Def_WangKangXue_SpectralTuran_IsSpectralExtremal
import Definitions.Def_WangKangXue_SpectralTuran_TuranPlusEdges
import Definitions.Def_WangKangXue_SpectralTuran_edgesIn
import Definitions.Def_WangKangXue_SpectralTuran_IsMaxCut
import Theorems.Thm_WangKangXue_SpectralTuran_lemma_3_6

set_option autoImplicit false

open Matrix in
theorem wk9_transpose {n : Type*} [Fintype n] {A : Matrix n n ℝ} (hA : A.IsHermitian) :
    Aᵀ = A := by
  rw [← conjTranspose_eq_transpose_of_trivial]; exact hA

open Matrix in
theorem wk9_parseval {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℝ}
    (hA : A.IsHermitian) (x y : n → ℝ) :
    x ⬝ᵥ y = ∑ j, (WithLp.ofLp (hA.eigenvectorBasis j) ⬝ᵥ x) *
      (WithLp.ofLp (hA.eigenvectorBasis j) ⬝ᵥ y) := by
  have := hA.eigenvectorBasis.sum_inner_mul_inner (WithLp.toLp 2 x) (WithLp.toLp 2 y)
  simp only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial] at this
  rw [dotProduct_comm x y, ← this]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [dotProduct_comm y]

open Matrix in
theorem wk9_eigdot {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℝ}
    (hA : A.IsHermitian) (j : n) (x : n → ℝ) :
    WithLp.ofLp (hA.eigenvectorBasis j) ⬝ᵥ (A *ᵥ x) =
      hA.eigenvalues j * (WithLp.ofLp (hA.eigenvectorBasis j) ⬝ᵥ x) := by
  rw [dotProduct_mulVec, ← mulVec_transpose, wk9_transpose hA, dotProduct_comm,
    hA.mulVec_eigenvectorBasis, dotProduct_smul, smul_eq_mul, dotProduct_comm]

open Matrix in
theorem wk9_le {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℝ}
    (hA : A.IsHermitian) (h : 0 < Fintype.card n) (x : n → ℝ) :
    x ⬝ᵥ (A *ᵥ x) ≤ hA.eigenvalues₀ ⟨0, h⟩ * (x ⬝ᵥ x) := by
  rw [wk9_parseval hA x (A *ᵥ x), wk9_parseval hA x x, Finset.mul_sum]
  refine Finset.sum_le_sum (fun j _ => ?_)
  rw [wk9_eigdot]
  have hj : hA.eigenvalues j ≤ hA.eigenvalues₀ ⟨0, h⟩ := by
    unfold Matrix.IsHermitian.eigenvalues
    exact hA.eigenvalues₀_antitone (by rw [Fin.le_def]; exact Nat.zero_le _)
  nlinarith [mul_le_mul_of_nonneg_right hj
    (mul_self_nonneg (WithLp.ofLp (hA.eigenvectorBasis j) ⬝ᵥ x))]

open Matrix in
theorem wk9_exists {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℝ}
    (hA : A.IsHermitian) (h : 0 < Fintype.card n) :
    ∃ v : n → ℝ, v ⬝ᵥ v = 1 ∧ A *ᵥ v = hA.eigenvalues₀ ⟨0, h⟩ • v := by
  obtain ⟨j, hj⟩ : ∃ j : n, j = (Fintype.equivOfCardEq (Fintype.card_fin _)) ⟨0, h⟩ :=
    ⟨_, rfl⟩
  refine ⟨WithLp.ofLp (hA.eigenvectorBasis j), ?_, ?_⟩
  · have horth := orthonormal_iff_ite.mp hA.eigenvectorBasis.orthonormal j j
    rw [EuclideanSpace.inner_eq_star_dotProduct] at horth
    simpa using horth
  · rw [hA.mulVec_eigenvectorBasis]
    congr 1
    rw [hj]
    simp only [Matrix.IsHermitian.eigenvalues, Equiv.symm_apply_apply]

open Matrix in
theorem wk9_quad {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (x : V → ℝ) :
    x ⬝ᵥ (G.adjMatrix ℝ *ᵥ x) = ∑ i, ∑ j, (if G.Adj i j then x i * x j else 0) := by
  simp only [dotProduct, mulVec, SimpleGraph.adjMatrix_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  split_ifs <;> ring

open Matrix in
theorem wk9_row {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (x : V → ℝ) (i : V) :
    (G.adjMatrix ℝ *ᵥ x) i = ∑ j, (if G.Adj i j then x j else 0) := by
  simp only [mulVec, dotProduct, SimpleGraph.adjMatrix_apply]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  split_ifs <;> ring
open Matrix in
theorem wk9_eq {n : Type*} [Fintype n] (A : Matrix n n ℝ) (hsym : Aᵀ = A) (lam : ℝ)
    (H : ∀ y : n → ℝ, y ⬝ᵥ (A *ᵥ y) ≤ lam * (y ⬝ᵥ y)) (x : n → ℝ)
    (hx : x ⬝ᵥ (A *ᵥ x) = lam * (x ⬝ᵥ x)) : A *ᵥ x = lam • x := by
  obtain ⟨w, hw⟩ : ∃ w, w = A *ᵥ x - lam • x := ⟨_, rfl⟩
  have hsymd : ∀ u z : n → ℝ, u ⬝ᵥ (A *ᵥ z) = z ⬝ᵥ (A *ᵥ u) := by
    intro u z
    rw [dotProduct_mulVec, ← mulVec_transpose, hsym, dotProduct_comm]
  have hp : w ⬝ᵥ (A *ᵥ x) - lam * (w ⬝ᵥ x) = w ⬝ᵥ w := by
    conv_rhs => rw [hw]
    rw [dotProduct_sub, dotProduct_smul, smul_eq_mul]
    conv_lhs => rw [hw]
  have hK := H w
  have hnn : 0 ≤ w ⬝ᵥ w := Finset.sum_nonneg (fun i _ => mul_self_nonneg (w i))
  have key : ∀ t : ℝ, 2 * t * (w ⬝ᵥ w) + t ^ 2 * (w ⬝ᵥ (A *ᵥ w) - lam * (w ⬝ᵥ w)) ≤ 0 := by
    intro t
    have h1 := H (x + t • w)
    simp only [mulVec_add, mulVec_smul, dotProduct_add, add_dotProduct, dotProduct_smul,
      smul_dotProduct, smul_eq_mul] at h1
    rw [hsymd x w, dotProduct_comm x w] at h1
    have e1 : t * (w ⬝ᵥ (A *ᵥ x)) - lam * (t * (w ⬝ᵥ x)) = t * (w ⬝ᵥ w) := by
      rw [← hp]; ring
    nlinarith [h1, hx, e1]
  have hw0 : w ⬝ᵥ w = 0 := by
    by_contra hne
    have hpos : 0 < w ⬝ᵥ w := lt_of_le_of_ne hnn (Ne.symm hne)
    obtain ⟨K, hKd⟩ : ∃ K, K = lam * (w ⬝ᵥ w) - w ⬝ᵥ (A *ᵥ w) := ⟨_, rfl⟩
    have hK0 : 0 ≤ K := by linarith
    have h2 := key ((w ⬝ᵥ w) / (K + 1))
    have hK1 : 0 < K + 1 := by linarith
    have e : (w ⬝ᵥ w) / (K + 1) * (K + 1) = w ⬝ᵥ w := div_mul_cancel₀ _ hK1.ne'
    obtain ⟨t, ht⟩ : ∃ t, t = (w ⬝ᵥ w) / (K + 1) := ⟨_, rfl⟩
    rw [← ht] at h2 e
    have htpos : 0 < t := by rw [ht]; positivity
    have : w ⬝ᵥ (A *ᵥ w) - lam * (w ⬝ᵥ w) = -K := by linarith
    rw [this] at h2
    nlinarith [mul_pos htpos hpos, mul_pos htpos htpos]
  have : w = 0 := dotProduct_self_eq_zero.mp hw0
  rw [hw] at this
  exact sub_eq_zero.mp this



section WKX37

open WangKangXue.SpectralTuran

theorem wkx_sum_card_part {n r : ℕ} (P : Fin n → Fin r) : ∑ i, (part P i).card = n := by
  classical
  have := Finset.card_eq_sum_card_fiberwise (s := (Finset.univ : Finset (Fin n)))
    (t := (Finset.univ : Finset (Fin r))) (f := P) (fun _ _ => Finset.mem_univ _)
  rw [Finset.card_univ, Fintype.card_fin] at this
  refine Eq.trans (Finset.sum_congr rfl (fun i _ => ?_)) this.symm
  unfold part
  congr


theorem wkx_mem_part {n r : ℕ} (P : Fin n → Fin r) (i : Fin r) (v : Fin n) :
    v ∈ part P i ↔ P v = i := by
  unfold part; simp


open Classical Matrix in
theorem wkx_perron_connected {n : ℕ} (G : SimpleGraph (Fin n)) (hG : G.Connected) :
    ∃ x : Fin n → ℝ, (G.adjMatrix ℝ).mulVec x = specRad G • x ∧ (∀ i, 0 < x i) ∧
      (∀ i, x i ≤ 1) ∧ ∃ z, x z = 1 := by
  obtain ⟨v0⟩ := hG.nonempty
  have hn0 : 0 < Fintype.card (Fin n) := Fintype.card_pos_iff.2 ⟨v0⟩
  have hsG : specRad G = (G.isHermitian_adjMatrix ℝ).eigenvalues₀ ⟨0, hn0⟩ := by
    unfold specRad; rw [dif_pos hn0]
  obtain ⟨v, hvv, hv⟩ := wk9_exists (G.isHermitian_adjMatrix ℝ) hn0
  rw [← hsG] at hv
  have hLe : ∀ y : Fin n → ℝ, y ⬝ᵥ (G.adjMatrix ℝ *ᵥ y) ≤ specRad G * (y ⬝ᵥ y) := by
    intro y
    rw [hsG]
    exact wk9_le (G.isHermitian_adjMatrix ℝ) hn0 y
  set y : Fin n → ℝ := fun i => |v i| with hy
  have hy0 : ∀ i, 0 ≤ y i := fun i => abs_nonneg _
  have hyy : y ⬝ᵥ y = 1 := by
    rw [← hvv, hy]
    simp only [dotProduct, abs_mul_abs_self]
  have hq : specRad G ≤ y ⬝ᵥ (G.adjMatrix ℝ *ᵥ y) := by
    have : v ⬝ᵥ (G.adjMatrix ℝ *ᵥ v) = specRad G := by
      rw [hv, dotProduct_smul, hvv, smul_eq_mul, mul_one]
    rw [← this, wk9_quad, wk9_quad]
    refine Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => ?_))
    split_ifs
    · rw [hy]; simp only [← abs_mul]; exact le_abs_self _
    · exact le_rfl
  have heq : y ⬝ᵥ (G.adjMatrix ℝ *ᵥ y) = specRad G * (y ⬝ᵥ y) := by
    have := hLe y
    rw [hyy, mul_one] at this ⊢
    linarith
  have hev := wk9_eq _ (wk9_transpose (G.isHermitian_adjMatrix ℝ)) (specRad G) hLe y heq
  -- positivity by zero propagation along walks
  have hprop : ∀ i j, y i = 0 → G.Adj i j → y j = 0 := by
    intro i j hi hij
    have hr := congrFun hev i
    rw [wk9_row, Pi.smul_apply, hi, smul_eq_mul, mul_zero] at hr
    have hnn : ∀ k ∈ Finset.univ, 0 ≤ (if G.Adj i k then y k else 0) := by
      intro k _; split_ifs
      · exact hy0 k
      · exact le_rfl
    have := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hr j (Finset.mem_univ _)
    rwa [if_pos hij] at this
  have hwalk : ∀ (u w : Fin n) (p : G.Walk u w), y u = 0 → y w = 0 := by
    intro u w p
    induction p with
    | nil => exact id
    | cons hadj _ ih => exact fun hu => ih (hprop _ _ hu hadj)
  have hypos : ∀ i, 0 < y i := by
    intro i
    rcases lt_or_eq_of_le (hy0 i) with h | h
    · exact h
    · exfalso
      have hall : ∀ k, y k = 0 := fun k => hwalk i k (hG.preconnected i k).some h.symm
      have : y ⬝ᵥ y = 0 := by simp [dotProduct, hall]
      rw [hyy] at this
      exact one_ne_zero this
  obtain ⟨z, -, hz⟩ := Finset.exists_max_image Finset.univ y ⟨v0, Finset.mem_univ _⟩
  have hyz : 0 < y z := hypos z
  refine ⟨(1 / y z) • y, ?_, ?_, ?_, ⟨z, ?_⟩⟩
  · rw [mulVec_smul, hev, smul_comm]
  · intro i
    simp only [Pi.smul_apply, smul_eq_mul]
    exact mul_pos (by positivity) (hypos i)
  · intro i
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [one_div, inv_mul_le_iff₀ hyz, mul_one]
    exact hz i (Finset.mem_univ _)
  · simp only [Pi.smul_apply, smul_eq_mul]
    field_simp


open Classical Matrix in
theorem wkx37_rayleigh {n : ℕ} (H : SimpleGraph (Fin n)) (hn : 0 < n) (y : Fin n → ℝ) :
    y ⬝ᵥ (H.adjMatrix ℝ *ᵥ y) ≤ specRad H * (y ⬝ᵥ y) := by
  have hn0 : 0 < Fintype.card (Fin n) := by simpa using hn
  have hs : specRad H = (H.isHermitian_adjMatrix ℝ).eigenvalues₀ ⟨0, hn0⟩ := by
    unfold specRad; rw [dif_pos hn0]
  rw [hs]
  exact wk9_le (H.isHermitian_adjMatrix ℝ) hn0 y

theorem wkx37_quad_mono {V : Type*} [Fintype V] (G H : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel H.Adj] (hGH : ∀ i j, G.Adj i j → H.Adj i j) (u w : V) (huw : u ≠ w)
    (hH : H.Adj u w) (hG : ¬ G.Adj u w) (x : V → ℝ) (hx : ∀ i, 0 < x i) :
    (∑ i, ∑ j, (if G.Adj i j then x i * x j else 0)) + 2 * (x u * x w) ≤
      ∑ i, ∑ j, (if H.Adj i j then x i * x j else 0) := by
  classical
  have hD : ∀ i j, 0 ≤ (if H.Adj i j then x i * x j else 0) -
      (if G.Adj i j then x i * x j else 0) := by
    intro i j
    by_cases hg : G.Adj i j
    · rw [if_pos (hGH i j hg), if_pos hg, sub_self]
    · rw [if_neg hg, sub_zero]
      split_ifs
      · exact (mul_pos (hx i) (hx j)).le
      · exact le_rfl
  have hsum : (∑ i, ∑ j, (if H.Adj i j then x i * x j else 0)) -
      (∑ i, ∑ j, (if G.Adj i j then x i * x j else 0)) =
      ∑ i, ∑ j, ((if H.Adj i j then x i * x j else 0) -
        (if G.Adj i j then x i * x j else 0)) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← Finset.sum_sub_distrib]
  have h1 : ∑ i ∈ ({u, w} : Finset V), ∑ j, ((if H.Adj i j then x i * x j else 0) -
        (if G.Adj i j then x i * x j else 0)) ≤
      ∑ i, ∑ j, ((if H.Adj i j then x i * x j else 0) -
        (if G.Adj i j then x i * x j else 0)) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun i _ _ => Finset.sum_nonneg (fun j _ => hD i j))
  rw [Finset.sum_pair huw] at h1
  have h2 := Finset.single_le_sum (fun j _ => hD u j) (Finset.mem_univ w)
  have h3 := Finset.single_le_sum (fun j _ => hD w j) (Finset.mem_univ u)
  rw [if_pos hH, if_neg hG, sub_zero] at h2
  rw [if_pos hH.symm, if_neg (fun h => hG h.symm), sub_zero] at h3
  have e : x w * x u = x u * x w := mul_comm _ _
  linarith

open Classical Matrix in
theorem wkx37_quad_adj {n : ℕ} (G H : SimpleGraph (Fin n))
    (hGH : ∀ i j, G.Adj i j → H.Adj i j) (u w : Fin n) (huw : u ≠ w)
    (hH : H.Adj u w) (hG : ¬ G.Adj u w) (x : Fin n → ℝ) (hx : ∀ i, 0 < x i) :
    x ⬝ᵥ (G.adjMatrix ℝ *ᵥ x) + 2 * (x u * x w) ≤ x ⬝ᵥ (H.adjMatrix ℝ *ᵥ x) := by
  rw [wk9_quad, wk9_quad]
  exact wkx37_quad_mono G H hGH u w huw hH hG x hx

open Classical Matrix in
theorem wkx37_strict {n : ℕ} (G : SimpleGraph (Fin n)) (hG : G.Connected) (u w : Fin n)
    (huw : u ≠ w) (hna : ¬ G.Adj u w) :
    specRad G < specRad (G ⊔ SimpleGraph.edge u w) := by
  obtain ⟨x, hev, hpos, -, -⟩ := wkx_perron_connected G hG
  have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) u.isLt
  have hR := wkx37_rayleigh (G ⊔ SimpleGraph.edge u w) hn x
  have hq := wkx37_quad_adj G (G ⊔ SimpleGraph.edge u w)
    (fun i j h => (SimpleGraph.sup_adj _ _ _ _).2 (Or.inl h)) u w huw
    ((SimpleGraph.sup_adj _ _ _ _).2 (Or.inr (by rw [SimpleGraph.edge_adj]; exact ⟨Or.inl ⟨rfl, rfl⟩, huw⟩)))
    hna x hpos
  rw [hev, dotProduct_smul, smul_eq_mul] at hq
  have hxx : 0 < x ⬝ᵥ x := by
    unfold dotProduct
    exact Finset.sum_pos (fun i _ => mul_pos (hpos i) (hpos i)) ⟨u, Finset.mem_univ _⟩
  have hp : 0 < x u * x w := mul_pos (hpos u) (hpos w)
  by_contra hcon
  push_neg at hcon
  nlinarith [mul_le_mul_of_nonneg_right hcon hxx.le]

open Classical in
theorem wkx37_le_edgesIn {V : Type*} [Fintype V] (G : SimpleGraph V) (S : Finset V)
    (T : Finset (Sym2 V)) (hT : ∀ e ∈ T, e ∈ G.edgeSet ∧ ∀ v ∈ e, v ∈ S) :
    T.card ≤ edgesIn G S := by
  unfold edgesIn
  rw [Finset.filter_congr_decidable]
  apply Finset.card_le_card
  intro e he
  rw [Finset.mem_filter, SimpleGraph.mem_edgeFinset]
  exact hT e he

open Classical in
theorem wkx37_nbr_part_le {n r : ℕ} (G : SimpleGraph (Fin n)) (P : Fin n → Fin r)
    (v : Fin n) (j : Fin r) (hv : P v = j) :
    ((G.neighborFinset v) ∩ part P j).card ≤ edgesIn G (part P j) := by
  have hinj : Function.Injective (fun y : Fin n => s(v, y)) := by
    intro y1 y2 h
    rcases Sym2.eq_iff.1 h with ⟨_, h⟩ | h
    · exact h
    · exact h.2.trans h.1
  rw [← Finset.card_image_of_injective _ hinj]
  refine wkx37_le_edgesIn G _ _ (fun e he => ?_)
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 he
  rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset] at hy
  refine ⟨hy.1, fun z hz => ?_⟩
  rcases Sym2.mem_iff.1 hz with rfl | rfl
  · rw [wkx_mem_part]; exact hv
  · exact hy.2

open Classical in
theorem wkx37_B_le {n r : ℕ} (G : SimpleGraph (Fin n)) (P : Fin n → Fin r) (i : Fin r) :
    ((part P i).filter (fun u => 1 ≤ ((G.neighborFinset u) ∩ part P i).card)).card
      ≤ 2 * edgesIn G (part P i) := by
  have hc : ∀ u ∈ (part P i).filter (fun u => 1 ≤ ((G.neighborFinset u) ∩ part P i).card),
      ∃ c, c ∈ (G.neighborFinset u) ∩ part P i := by
    intro u hu
    rw [Finset.mem_filter] at hu
    exact Finset.card_pos.1 hu.2
  choose! c hc using hc
  refine (Finset.card_le_mul_card_image (f := fun u => s(u, c u)) _ 2 ?_).trans
    (Nat.mul_le_mul_left 2 (wkx37_le_edgesIn G _ _ ?_))
  · intro e _
    induction e using Sym2.ind with
    | h p q =>
      refine le_trans (Finset.card_le_card (t := ({p, q} : Finset (Fin n))) ?_)
        Finset.card_le_two
      intro x hx
      rw [Finset.mem_filter] at hx
      have hm : x ∈ s(p, q) := by rw [← hx.2]; exact Sym2.mem_mk_left _ _
      rcases Sym2.mem_iff.1 hm with rfl | rfl
      · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  · intro e he
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 he
    have hcu := hc u hu
    have hu' := (Finset.mem_filter.1 hu).1
    rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset] at hcu
    refine ⟨hcu.1, fun z hz => ?_⟩
    rcases Sym2.mem_iff.1 hz with rfl | rfl
    · exact hu'
    · exact hcu.2

open Classical in
theorem wkx37_deg {n r : ℕ} (G : SimpleGraph (Fin n)) (P : Fin n → Fin r) (a : ℕ)
    (hin : ∀ i, edgesIn G (part P i) ≤ a) (v : Fin n) (T : Finset (Fin n))
    (hT : ∀ t ∈ T, P t ≠ P v) :
    G.degree v + (T \ G.neighborFinset v).card + (part P (P v)).card ≤ a + n := by
  have h1 := wkx37_nbr_part_le G P v (P v) rfl
  have h2 := hin (P v)
  have hsplit := Finset.card_inter_add_card_sdiff (G.neighborFinset v) (part P (P v))
  rw [SimpleGraph.card_neighborFinset_eq_degree] at hsplit
  have hd2 : Disjoint (G.neighborFinset v \ part P (P v)) (T \ G.neighborFinset v) := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    exact (Finset.mem_sdiff.1 hx2).2 (Finset.mem_sdiff.1 hx1).1
  have hdisj : Disjoint ((G.neighborFinset v \ part P (P v)) ∪ (T \ G.neighborFinset v))
      (part P (P v)) := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    rcases Finset.mem_union.1 hx1 with h | h
    · exact (Finset.mem_sdiff.1 h).2 hx2
    · exact hT x (Finset.mem_sdiff.1 h).1 ((wkx_mem_part P (P v) x).1 hx2)
  have hcard : ((G.neighborFinset v \ part P (P v)) ∪ (T \ G.neighborFinset v) ∪
      part P (P v)).card ≤ n := by
    simpa using Finset.card_le_univ
      ((G.neighborFinset v \ part P (P v)) ∪ (T \ G.neighborFinset v) ∪ part P (P v))
  rw [Finset.card_union_of_disjoint hdisj, Finset.card_union_of_disjoint hd2] at hcard
  omega

open Classical in
theorem wkx37_find {n r : ℕ} (G : SimpleGraph (Fin n)) (P : Fin n → Fin r) (k : Fin r) (M : ℝ)
    (hM : ∀ y, P y ≠ k → ((part P k \ G.neighborFinset y).card : ℝ) ≤ M)
    (S X : Finset (Fin n)) (hS : ∀ y ∈ S, P y ≠ k)
    (hbig : (X.card : ℝ) + S.card * M < (part P k).card) :
    ∃ c ∈ part P k, c ∉ X ∧ ∀ y ∈ S, G.Adj y c := by
  have e1 : (X ∪ S.biUnion (fun y => part P k \ G.neighborFinset y)).card ≤
      X.card + (S.biUnion (fun y => part P k \ G.neighborFinset y)).card :=
    Finset.card_union_le _ _
  have e2 : (S.biUnion (fun y => part P k \ G.neighborFinset y)).card ≤
      ∑ y ∈ S, (part P k \ G.neighborFinset y).card := Finset.card_biUnion_le
  have e3 : ((∑ y ∈ S, (part P k \ G.neighborFinset y).card : ℕ) : ℝ) ≤ S.card * M := by
    push_cast
    calc ∑ y ∈ S, ((part P k \ G.neighborFinset y).card : ℝ) ≤ ∑ _y ∈ S, M :=
          Finset.sum_le_sum (fun y hy => hM y (hS y hy))
      _ = S.card * M := by rw [Finset.sum_const, nsmul_eq_mul]
  have e4 : ((X ∪ S.biUnion (fun y => part P k \ G.neighborFinset y)).card : ℝ) ≤
      X.card + ((∑ y ∈ S, (part P k \ G.neighborFinset y).card : ℕ) : ℝ) := by
    exact_mod_cast e1.trans (Nat.add_le_add_left e2 _)
  have hlt : (X ∪ S.biUnion (fun y => part P k \ G.neighborFinset y)).card <
      (part P k).card := by
    have : ((X ∪ S.biUnion (fun y => part P k \ G.neighborFinset y)).card : ℝ) <
        (part P k).card := by linarith
    exact_mod_cast this
  obtain ⟨c, hc, hcb⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  refine ⟨c, hc, fun h => hcb (Finset.mem_union_left _ h), fun y hy => ?_⟩
  by_contra hna
  apply hcb
  refine Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨y, hy, ?_⟩)
  rw [Finset.mem_sdiff, SimpleGraph.mem_neighborFinset]
  exact ⟨hc, hna⟩

theorem wkx37_ne {r : ℕ} (hr : 2 ≤ r) (j : Fin r) : ∃ l : Fin r, l ≠ j := by
  by_cases h : j.val = 0
  · exact ⟨⟨1, by omega⟩, fun e => by rw [← e] at h; simp at h⟩
  · exact ⟨⟨0, by omega⟩, fun e => h (by rw [← e])⟩

open Classical in
theorem wkx37_core {W : Type*} [Fintype W] (F : SimpleGraph W) {n r a : ℕ} (hr : 2 ≤ r)
    (G : SimpleGraph (Fin n)) (hG : IsSpectralExtremal F G) (P : Fin n → Fin r) (δ : ℝ)
    (hδ : 0 ≤ δ)
    (hdeg : ∀ v : Fin n, (1 - 1 / (r : ℝ) - δ) * n < (G.degree v : ℝ))
    (hin : ∀ i : Fin r, edgesIn G (part P i) ≤ a)
    (hbig : ((Fintype.card W : ℝ) + 2) * ((r : ℝ) * a + r * δ * n + 1) <
      (1 / (r : ℝ) - (r - 1) * δ) * n - (r - 1) * a) (i : Fin r) :
    ((part P i).filter (fun u => 1 ≤ ((G.neighborFinset u) ∩ part P i).card)).card
        ≤ 2 * a ∧
    ∀ u ∈ (part P i).filter (fun u => ((G.neighborFinset u) ∩ part P i).card = 0),
      ∀ w : Fin n, P w ≠ i → G.Adj u w := by
  have hr0 : (0:ℝ) < r := by exact_mod_cast (by omega : 0 < r)
  have hq : (r:ℝ) * (1 / r) = 1 := by field_simp
  have hqn : (r:ℝ) * (1 / r) * n = n := by rw [hq, one_mul]
  have hk0 : (0:ℝ) ≤ Fintype.card W := Nat.cast_nonneg _
  have hn0 : (0:ℝ) ≤ n := Nat.cast_nonneg _
  have hM0 : (0:ℝ) ≤ (r : ℝ) * a + r * δ * n := by positivity
  -- upper bound on every part
  have hup : ∀ j : Fin r, ((part P j).card : ℝ) ≤ a + (1 / r + δ) * n := by
    intro j
    rcases (part P j).eq_empty_or_nonempty with h | ⟨v, hv⟩
    · rw [h, Finset.card_empty, Nat.cast_zero]; positivity
    · have hPv : P v = j := (wkx_mem_part P j v).1 hv
      have h1 := wkx37_deg G P a hin v ∅ (by simp)
      rw [hPv] at h1
      simp only [Finset.empty_sdiff, Finset.card_empty, add_zero] at h1
      have h1' : (G.degree v : ℝ) + (part P j).card ≤ a + n := by exact_mod_cast h1
      have := hdeg v
      linarith
  -- lower bound on every part
  have hlow : ∀ j : Fin r,
      (1 / (r : ℝ) - (r - 1) * δ) * n - (r - 1) * a ≤ (part P j).card := by
    intro j
    have hs := wkx_sum_card_part P
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)] at hs
    have hs' : (n : ℝ) = (part P j).card +
        ∑ l ∈ Finset.univ.erase j, ((part P l).card : ℝ) := by exact_mod_cast hs.symm
    have hb : ∑ l ∈ Finset.univ.erase j, ((part P l).card : ℝ) ≤
        ∑ _l ∈ Finset.univ.erase j, ((a:ℝ) + (1 / r + δ) * n) :=
      Finset.sum_le_sum (fun l _ => hup l)
    rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, Nat.cast_sub (by omega : 1 ≤ r)] at hb
    push_cast at hb
    linarith
  -- few non-neighbours in any other part
  have hnon : ∀ (k : Fin r) (y : Fin n), P y ≠ k →
      ((part P k \ G.neighborFinset y).card : ℝ) ≤ (r : ℝ) * a + r * δ * n := by
    intro k y hy
    have h1 := wkx37_deg G P a hin y (part P k)
      (fun t ht => by rw [(wkx_mem_part P k t).1 ht]; exact Ne.symm hy)
    have h1' : (G.degree y : ℝ) + (part P k \ G.neighborFinset y).card +
        (part P (P y)).card ≤ a + n := by exact_mod_cast h1
    have h2 := hlow (P y)
    have h3 := hdeg y
    linarith
  have hfind : ∀ (k : Fin r) (S X : Finset (Fin n)), (∀ y ∈ S, P y ≠ k) →
      (X.card : ℝ) + S.card * ((r : ℝ) * a + r * δ * n) ≤
        ((Fintype.card W : ℝ) + 2) * ((r : ℝ) * a + r * δ * n + 1) →
      ∃ c ∈ part P k, c ∉ X ∧ ∀ y ∈ S, G.Adj y c := by
    intro k S X hS hle
    exact wkx37_find G P k _ (fun y hy => hnon k y hy) S X hS (by linarith [hlow k])
  have hcommon : ∀ (k : Fin r) (y z : Fin n), P y ≠ k → P z ≠ k →
      ∃ c, G.Adj y c ∧ G.Adj z c := by
    intro k y z hy hz
    have h2 : (({y, z} : Finset (Fin n)).card : ℝ) ≤ 2 := by exact_mod_cast Finset.card_le_two
    obtain ⟨c, -, -, hc⟩ := hfind k {y, z} ∅
      (by
        intro t ht
        rcases Finset.mem_insert.1 ht with rfl | ht
        · exact hy
        · rw [Finset.mem_singleton.1 ht]; exact hz)
      (by
        simp only [Finset.card_empty, Nat.cast_zero, zero_add]
        nlinarith [mul_le_mul_of_nonneg_right h2 hM0, mul_nonneg hk0 hM0])
    exact ⟨c, hc y (by simp), hc z (by simp)⟩
  have hadj1 : ∀ (k : Fin r) (y : Fin n), P y ≠ k → ∃ c, P c = k ∧ G.Adj y c := by
    intro k y hy
    obtain ⟨c, hc, -, hcy⟩ := hfind k {y} ∅
      (by intro t ht; rw [Finset.mem_singleton.1 ht]; exact hy)
      (by
        simp only [Finset.card_empty, Nat.cast_zero, zero_add, Finset.card_singleton,
          Nat.cast_one, one_mul]
        nlinarith [mul_nonneg hk0 hM0])
    exact ⟨c, (wkx_mem_part P k c).1 hc, hcy y (Finset.mem_singleton_self _)⟩
  have hpre : G.Preconnected := by
    intro y z
    obtain ⟨k, hk⟩ := wkx37_ne hr (P y)
    by_cases hz : P z = k
    · obtain ⟨c, hc, hyc⟩ := hadj1 k y (Ne.symm hk)
      obtain ⟨l, hl⟩ := wkx37_ne hr k
      obtain ⟨d, hcd, hzd⟩ := hcommon l c z (by rw [hc]; exact Ne.symm hl)
        (by rw [hz]; exact Ne.symm hl)
      exact hyc.reachable.trans (hcd.reachable.trans hzd.reachable.symm)
    · obtain ⟨d, hyd, hzd⟩ := hcommon k y z (Ne.symm hk) hz
      exact hyd.reachable.trans hzd.reachable.symm
  refine ⟨(wkx37_B_le G P i).trans (by have := hin i; omega), ?_⟩
  intro u hu w hw
  rw [Finset.mem_filter] at hu
  have hPu : P u = i := (wkx_mem_part P i u).1 hu.1
  have hu0 : ∀ y, G.Adj u y → P y ≠ i := by
    intro y hy hPy
    have hmem : y ∈ G.neighborFinset u ∩ part P i :=
      Finset.mem_inter.2 ⟨(SimpleGraph.mem_neighborFinset _ _ _).2 hy,
        (wkx_mem_part P i y).2 hPy⟩
    rw [Finset.card_eq_zero.1 hu.2] at hmem
    simp at hmem
  by_contra hna
  have huw : u ≠ w := fun h => hw (h ▸ hPu)
  have hconn : G.Connected := (SimpleGraph.connected_iff G).2 ⟨hpre, ⟨u⟩⟩
  have hlt := wkx37_strict G hconn u w huw hna
  have hnotfree : ¬ F.Free (G ⊔ SimpleGraph.edge u w) :=
    fun hf => absurd (hG.2 _ hf) (not_le.2 hlt)
  obtain ⟨f⟩ := not_not.1 hnotfree
  apply hG.1
  have hX : ((Finset.univ.image f.toHom).card : ℝ) ≤ Fintype.card W := by
    exact_mod_cast (Finset.card_image_le.trans (by rw [Finset.card_univ]))
  have hS : (((Finset.univ.image f.toHom).filter (fun y => P y ≠ i)).card : ℝ) ≤
      Fintype.card W := by
    exact_mod_cast ((Finset.card_filter_le _ _).trans
      (Finset.card_image_le.trans (by rw [Finset.card_univ])))
  obtain ⟨c, hc, hcX, hcS⟩ := hfind i ((Finset.univ.image f.toHom).filter (fun y => P y ≠ i))
    (Finset.univ.image f.toHom) (fun y hy => (Finset.mem_filter.1 hy).2)
    (by nlinarith [mul_le_mul_of_nonneg_right hS hM0])
  have hcS' : ∀ q : W, P (f.toHom q) ≠ i → G.Adj (f.toHom q) c := fun q hq =>
    hcS _ (Finset.mem_filter.2 ⟨Finset.mem_image_of_mem _ (Finset.mem_univ q), hq⟩)
  have hcX' : ∀ q : W, f.toHom q ≠ c := fun q hq =>
    hcX (hq ▸ Finset.mem_image_of_mem _ (Finset.mem_univ q))
  refine ⟨⟨⟨fun p => if f.toHom p = u then c else f.toHom p, ?_⟩, ?_⟩⟩
  · intro p q hpq
    have hf := f.toHom.map_adj hpq
    rw [SimpleGraph.sup_adj, SimpleGraph.edge_adj] at hf
    split_ifs with h1 h2 h2
    · exact absurd (f.injective (h1.trans h2.symm)) (F.ne_of_adj hpq)
    · have hfq : P (f.toHom q) ≠ i := by
        rcases hf with hf | ⟨hf, -⟩
        · rw [h1] at hf; exact hu0 _ hf
        · rcases hf with ⟨-, hq⟩ | ⟨hp, -⟩
          · rw [hq]; exact hw
          · exact absurd (h1.symm.trans hp) huw
      exact (hcS' q hfq).symm
    · have hfp : P (f.toHom p) ≠ i := by
        rcases hf with hf | ⟨hf, -⟩
        · rw [h2] at hf; exact hu0 _ hf.symm
        · rcases hf with ⟨hp, -⟩ | ⟨hp, -⟩
          · exact absurd hp h1
          · rw [hp]; exact hw
      exact hcS' p hfp
    · rcases hf with hf | ⟨hf, -⟩
      · exact hf
      · rcases hf with ⟨hp, -⟩ | ⟨-, hq⟩
        · exact absurd hp h1
        · exact absurd hq h2
  · intro p q hpq
    change (if f.toHom p = u then c else f.toHom p) =
      (if f.toHom q = u then c else f.toHom q) at hpq
    split_ifs at hpq with h1 h2 h2
    · exact f.injective (h1.trans h2.symm)
    · exact absurd hpq.symm (hcX' q)
    · exact absurd hpq (hcX' p)
    · exact f.injective hpq

theorem wkx37_arith (r a k n δ : ℝ) (hr : 2 ≤ r) (hδ : 0 ≤ δ) (hk : 0 ≤ k) (ha : 0 ≤ a)
    (hδ' : (k + 3) * r * δ ≤ 1 / (2 * r))
    (hn : 2 * r * ((r - 1) * a + (k + 2) * (r * a + 1)) + 1 ≤ n) :
    (k + 2) * (r * a + r * δ * n + 1) < (1 / r - (r - 1) * δ) * n - (r - 1) * a := by
  have hr0 : 0 < r := by linarith
  have hC0 : 0 ≤ (r - 1) * a + (k + 2) * (r * a + 1) := by
    have : 0 ≤ r - 1 := by linarith
    positivity
  have hn0 : 0 ≤ n := by nlinarith
  set s : ℝ := 1 / (2 * r) with hsdef
  have hs : 0 < s := by positivity
  have h2rs : 2 * r * s = 1 := by rw [hsdef]; field_simp
  have h1r : 1 / r = 2 * s := by rw [hsdef]; field_simp
  have h1 : (k + 3) * r * δ * n ≤ s * n := mul_le_mul_of_nonneg_right hδ' hn0
  have hC : s * (2 * r * ((r - 1) * a + (k + 2) * (r * a + 1))) =
      (r - 1) * a + (k + 2) * (r * a + 1) := by
    rw [show s * (2 * r * ((r - 1) * a + (k + 2) * (r * a + 1))) =
      (2 * r * s) * ((r - 1) * a + (k + 2) * (r * a + 1)) by ring, h2rs, one_mul]
  have h3 := mul_le_mul_of_nonneg_left hn hs.le
  rw [h1r]
  nlinarith [mul_nonneg hδ hn0]

open Classical in
theorem wkx37_from36 {W : Type*} [Fintype W] (F : SimpleGraph W) (r a : ℕ) (hr : 2 ≤ r)
    (h36 : ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ G : SimpleGraph (Fin n), IsSpectralExtremal F G →
        ∀ P : Fin n → Fin r, IsMaxCut G P →
          (∀ v : Fin n,
            (1 - 1 / (r : ℝ) - 3 * r * ε ^ ((1 : ℝ) / 3)) * n < (G.degree v : ℝ)) ∧
          ∀ i : Fin r, edgesIn G (part P i) ≤ a) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ G : SimpleGraph (Fin n), IsSpectralExtremal F G →
      ∀ P : Fin n → Fin r, IsMaxCut G P → ∀ i : Fin r,
        ((part P i).filter (fun u => 1 ≤ ((G.neighborFinset u) ∩ part P i).card)).card
            ≤ 2 * a ∧
        ∀ u ∈ (part P i).filter (fun u => ((G.neighborFinset u) ∩ part P i).card = 0),
          ∀ w : Fin n, P w ≠ i → G.Adj u w := by
  obtain ⟨ε₀, hε₀, h⟩ := h36
  have hk0 : (0:ℝ) ≤ Fintype.card W := Nat.cast_nonneg _
  have hr0 : (0:ℝ) < r := by exact_mod_cast (by omega : 0 < r)
  have hr2 : (2:ℝ) ≤ r := by exact_mod_cast hr
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = 1 / (6 * (r:ℝ) ^ 3 * ((Fintype.card W : ℝ) + 3)) := ⟨_, rfl⟩
  have htpos : 0 < t := by rw [ht]; positivity
  obtain ⟨ε, hε⟩ : ∃ ε : ℝ, ε = min (ε₀ / 2) (t ^ 3) := ⟨_, rfl⟩
  have hεpos : 0 < ε := by rw [hε]; exact lt_min (by linarith) (by positivity)
  have hεlt : ε < ε₀ := by rw [hε]; exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hroot : ε ^ ((1:ℝ) / 3) ≤ t := by
    calc ε ^ ((1:ℝ) / 3) ≤ (t ^ 3) ^ ((1:ℝ) / 3) :=
          Real.rpow_le_rpow hεpos.le (by rw [hε]; exact min_le_right _ _) (by norm_num)
      _ = t := by
          rw [show ((1:ℝ) / 3) = ((3:ℕ):ℝ)⁻¹ by norm_num]
          exact Real.pow_rpow_inv_natCast htpos.le (by norm_num)
  have hδ0 : 0 ≤ 3 * (r:ℝ) * ε ^ ((1:ℝ) / 3) := by positivity
  have hδ' : ((Fintype.card W : ℝ) + 3) * r * (3 * (r:ℝ) * ε ^ ((1:ℝ) / 3)) ≤ 1 / (2 * r) := by
    calc ((Fintype.card W : ℝ) + 3) * r * (3 * (r:ℝ) * ε ^ ((1:ℝ) / 3))
        ≤ ((Fintype.card W : ℝ) + 3) * r * (3 * (r:ℝ) * t) := by gcongr
      _ = 1 / (2 * r) := by rw [ht]; field_simp; ring
  obtain ⟨n₀, hn₀⟩ := h ε hεpos hεlt
  obtain ⟨N1, hN1⟩ := exists_nat_ge
    (2 * (r:ℝ) * (((r:ℝ) - 1) * a + ((Fintype.card W : ℝ) + 2) * ((r:ℝ) * a + 1)) + 1)
  refine ⟨max n₀ N1, fun n hn G hG P hP i => ?_⟩
  obtain ⟨hdeg, hin⟩ := hn₀ n (le_of_max_le_left hn) G hG P hP
  have hnN : (N1 : ℝ) ≤ n := by exact_mod_cast le_of_max_le_right hn
  exact wkx37_core F hr G hG P _ hδ0 hdeg hin
    (wkx37_arith r a (Fintype.card W) n _ hr2 hδ0 hk0 (Nat.cast_nonneg _) hδ'
      (hN1.trans hnN)) i

-- ===== Lemma 3.8 (twin-insertion argument) =====

open Classical in
theorem wkx38_low {n r a : ℕ} (hr : 2 ≤ r) (G : SimpleGraph (Fin n)) (P : Fin n → Fin r)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hdeg : ∀ v : Fin n, (1 - 1 / (r : ℝ) - δ) * n < (G.degree v : ℝ))
    (hin : ∀ i : Fin r, edgesIn G (part P i) ≤ a) (j : Fin r) :
    (1 / (r : ℝ) - (r - 1) * δ) * n - (r - 1) * a ≤ (part P j).card := by
  have hr0 : (0:ℝ) < r := by exact_mod_cast (by omega : 0 < r)
  have hn0 : (0:ℝ) ≤ n := Nat.cast_nonneg _
  have hup : ∀ j : Fin r, ((part P j).card : ℝ) ≤ a + (1 / r + δ) * n := by
    intro j
    rcases (part P j).eq_empty_or_nonempty with h | ⟨v, hv⟩
    · rw [h, Finset.card_empty, Nat.cast_zero]; positivity
    · have hPv : P v = j := (wkx_mem_part P j v).1 hv
      have h1 := wkx37_deg G P a hin v ∅ (by simp)
      rw [hPv] at h1
      simp only [Finset.empty_sdiff, Finset.card_empty, add_zero] at h1
      have h1' : (G.degree v : ℝ) + (part P j).card ≤ a + n := by exact_mod_cast h1
      have := hdeg v
      linarith
  have hs := wkx_sum_card_part P
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)] at hs
  have hs' : (n : ℝ) = (part P j).card +
      ∑ l ∈ Finset.univ.erase j, ((part P l).card : ℝ) := by exact_mod_cast hs.symm
  have hb : ∑ l ∈ Finset.univ.erase j, ((part P l).card : ℝ) ≤
      ∑ _l ∈ Finset.univ.erase j, ((a:ℝ) + (1 / r + δ) * n) :=
    Finset.sum_le_sum (fun l _ => hup l)
  rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, Nat.cast_sub (by omega : 1 ≤ r)] at hb
  push_cast at hb
  have hq : (r:ℝ) * (1 / r) = 1 := by field_simp
  nlinarith

/-- `G` with the edges at `u` replaced by all edges from `u` to the vertices outside part `i`. -/
def wkx38G {n r : ℕ} (G : SimpleGraph (Fin n)) (P : Fin n → Fin r) (u : Fin n) (i : Fin r) :
    SimpleGraph (Fin n) where
  Adj p q := p ≠ q ∧ ((p ≠ u ∧ q ≠ u ∧ G.Adj p q) ∨ (p = u ∧ P q ≠ i) ∨ (q = u ∧ P p ≠ i))
  symm := ⟨fun p q h => ⟨Ne.symm h.1, by
    rcases h.2 with ⟨h1, h2, h3⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨h2, h1, h3.symm⟩
    · exact Or.inr (Or.inr ⟨h1, h2⟩)
    · exact Or.inr (Or.inl ⟨h1, h2⟩)⟩⟩
  loopless := ⟨fun p h => h.1 rfl⟩

theorem wkx38G_adj {n r : ℕ} (G : SimpleGraph (Fin n)) (P : Fin n → Fin r) (u : Fin n)
    (i : Fin r) (p q : Fin n) :
    (wkx38G G P u i).Adj p q ↔
      p ≠ q ∧ ((p ≠ u ∧ q ≠ u ∧ G.Adj p q) ∨ (p = u ∧ P q ≠ i) ∨ (q = u ∧ P p ≠ i)) :=
  Iff.rfl

theorem wkx38_free {W : Type*} [Fintype W] (F : SimpleGraph W) {n r : ℕ}
    (G : SimpleGraph (Fin n)) (hG : F.Free G) (P : Fin n → Fin r) (u : Fin n) (i : Fin r)
    (C : Finset (Fin n)) (hC : Fintype.card W + 2 ≤ C.card)
    (hCadj : ∀ c ∈ C, ∀ w, P w ≠ i → G.Adj c w) :
    F.Free (wkx38G G P u i) := by
  classical
  rintro ⟨f⟩
  apply hG
  have hlt : (insert u (Finset.univ.image f.toHom)).card < C.card := by
    have h1 := Finset.card_insert_le u (Finset.univ.image f.toHom)
    have h2 : (Finset.univ.image f.toHom).card ≤ Fintype.card W :=
      Finset.card_image_le.trans (by rw [Finset.card_univ])
    omega
  obtain ⟨c, hc, hcX⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  have hcX' : ∀ q : W, f.toHom q ≠ c := fun q hq =>
    hcX (Finset.mem_insert_of_mem (hq ▸ Finset.mem_image_of_mem _ (Finset.mem_univ q)))
  refine ⟨⟨⟨fun p => if f.toHom p = u then c else f.toHom p, ?_⟩, ?_⟩⟩
  · intro p q hpq
    have hf : (wkx38G G P u i).Adj (f.toHom p) (f.toHom q) := f.toHom.map_adj hpq
    rw [wkx38G_adj] at hf
    change G.Adj (if f.toHom p = u then c else f.toHom p)
      (if f.toHom q = u then c else f.toHom q)
    split_ifs with h1 h2 h2
    · exact absurd (f.injective (h1.trans h2.symm)) (F.ne_of_adj hpq)
    · have hq : P (f.toHom q) ≠ i := by
        rcases hf.2 with ⟨h3, -, -⟩ | ⟨-, h4⟩ | ⟨h4, -⟩
        · exact absurd h1 h3
        · exact h4
        · exact absurd h4 h2
      exact hCadj c hc _ hq
    · have hp : P (f.toHom p) ≠ i := by
        rcases hf.2 with ⟨-, h3, -⟩ | ⟨h4, -⟩ | ⟨-, h4⟩
        · exact absurd h2 h3
        · exact absurd h4 h1
        · exact h4
      exact (hCadj c hc _ hp).symm
    · rcases hf.2 with ⟨-, -, h3⟩ | ⟨h4, -⟩ | ⟨h4, -⟩
      · exact h3
      · exact absurd h4 h1
      · exact absurd h4 h2
  · intro p q hpq
    change (if f.toHom p = u then c else f.toHom p) =
      (if f.toHom q = u then c else f.toHom q) at hpq
    split_ifs at hpq with h1 h2 h2
    · exact f.injective (h1.trans h2.symm)
    · exact absurd hpq.symm (hcX' q)
    · exact absurd hpq (hcX' p)
    · exact f.injective hpq

theorem wkx38_quad_diff {V : Type*} [Fintype V] [DecidableEq V] (G H : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H.Adj] (u : V)
    (hagree : ∀ p q, p ≠ u → q ≠ u → (H.Adj p q ↔ G.Adj p q)) (x : V → ℝ) :
    (∑ p, ∑ q, (if H.Adj p q then x p * x q else 0)) -
        (∑ p, ∑ q, (if G.Adj p q then x p * x q else 0)) =
      2 * x u * ((∑ q, (if H.Adj u q then x q else 0)) -
        ∑ q, (if G.Adj u q then x q else 0)) := by
  obtain ⟨D, hD⟩ : ∃ D : V → V → ℝ, D = fun p q =>
      (if H.Adj p q then x p * x q else 0) - (if G.Adj p q then x p * x q else 0) := ⟨_, rfl⟩
  have hsum : (∑ p, ∑ q, (if H.Adj p q then x p * x q else 0)) -
      (∑ p, ∑ q, (if G.Adj p q then x p * x q else 0)) = ∑ p, ∑ q, D p q := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [← Finset.sum_sub_distrib, hD]
  have hDuu : D u u = 0 := by
    rw [hD]; simp only [SimpleGraph.irrefl, if_false, sub_self]
  have hDsymm : ∀ p q, D p q = D q p := by
    intro p q
    rw [hD]
    simp only [H.adj_comm q p, G.adj_comm q p, mul_comm (x q) (x p)]
  have hrow : ∀ p, ∑ q, D p q = (if p = u then ∑ q, D u q else 0) + D p u := by
    intro p
    by_cases hp : p = u
    · subst hp; rw [if_pos rfl, hDuu, add_zero]
    · rw [if_neg hp, zero_add]
      rw [Finset.sum_eq_single u]
      · intro q _ hq
        rw [hD]
        simp only [hagree p q hp hq, sub_self]
      · intro h; exact absurd (Finset.mem_univ u) h
  have hS : ∑ q, D u q = x u * ((∑ q, (if H.Adj u q then x q else 0)) -
      ∑ q, (if G.Adj u q then x q else 0)) := by
    rw [mul_sub, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun q _ => ?_)
    rw [hD]
    simp only
    split_ifs <;> ring
  have hcol : ∑ p, D p u = ∑ q, D u q :=
    Finset.sum_congr rfl (fun p _ => hDsymm p u)
  rw [hsum, Finset.sum_congr rfl (fun p _ => hrow p), Finset.sum_add_distrib, hcol]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [hS]
  ring

open Classical Matrix in
theorem wkx38_key {n r : ℕ} (G : SimpleGraph (Fin n)) (P : Fin n → Fin r) (u : Fin n)
    (i : Fin r) (hle : specRad (wkx38G G P u i) ≤ specRad G) (x : Fin n → ℝ)
    (hev : (G.adjMatrix ℝ).mulVec x = specRad G • x) (hpos : ∀ j, 0 < x j) :
    (∑ q, (if P q ≠ i then x q else 0)) ≤ (specRad G + 1) * x u := by
  have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) u.isLt
  have hR := wkx37_rayleigh (wkx38G G P u i) hn x
  have hxx : 0 < x ⬝ᵥ x := by
    unfold dotProduct
    exact Finset.sum_pos (fun j _ => mul_pos (hpos j) (hpos j)) ⟨u, Finset.mem_univ _⟩
  have hA : x ⬝ᵥ (G.adjMatrix ℝ *ᵥ x) = specRad G * (x ⬝ᵥ x) := by
    rw [hev, dotProduct_smul, smul_eq_mul]
  have hrow : ∑ q, (if G.Adj u q then x q else 0) = specRad G * x u := by
    rw [← wk9_row G x u, hev]; simp
  rw [wk9_quad] at hR hA
  have hdiff := wkx38_quad_diff G (wkx38G G P u i) u
    (fun p q hp hq => by
      rw [wkx38G_adj]
      constructor
      · rintro ⟨-, h | ⟨h, -⟩ | ⟨h, -⟩⟩
        · exact h.2.2
        · exact absurd h hp
        · exact absurd h hq
      · intro h; exact ⟨G.ne_of_adj h, Or.inl ⟨hp, hq, h⟩⟩) x
  have hHrow : (∑ q, (if P q ≠ i then x q else 0)) ≤
      (∑ q, (if (wkx38G G P u i).Adj u q then x q else 0)) + x u := by
    have h1 : ∀ q, (if P q ≠ i then x q else 0) ≤
        (if (wkx38G G P u i).Adj u q then x q else 0) + (if q = u then x q else 0) := by
      intro q
      by_cases hq : q = u
      · subst hq
        have hl : ¬ (wkx38G G P q i).Adj q q := (wkx38G G P q i).irrefl
        rw [if_neg hl, if_pos rfl, zero_add]
        split_ifs
        · exact le_rfl
        · exact (hpos q).le
      · rw [if_neg hq, add_zero]
        by_cases hPq : P q ≠ i
        · have hadj : (wkx38G G P u i).Adj u q := by
            rw [wkx38G_adj]; exact ⟨Ne.symm hq, Or.inr (Or.inl ⟨rfl, hPq⟩)⟩
          rw [if_pos hPq, if_pos hadj]
        · rw [if_neg hPq]
          split_ifs
          · exact (hpos q).le
          · exact le_rfl
    have h2 := Finset.sum_le_sum (fun q (_ : q ∈ Finset.univ) => h1 q)
    rw [Finset.sum_add_distrib] at h2
    simpa only [Finset.sum_ite_eq', Finset.mem_univ, if_true] using h2
  have h1 : specRad (wkx38G G P u i) * (x ⬝ᵥ x) ≤ specRad G * (x ⬝ᵥ x) :=
    mul_le_mul_of_nonneg_right hle hxx.le
  have hRH : (∑ q, (if (wkx38G G P u i).Adj u q then x q else 0)) ≤ specRad G * x u := by
    by_contra hcon
    push Not at hcon
    have hp := mul_pos (mul_pos (two_pos : (0:ℝ) < 2) (hpos u)) (sub_pos.2 hcon)
    rw [hrow] at hdiff
    linarith
  linarith

open Classical in
theorem wkx38_top {n r a : ℕ} (G : SimpleGraph (Fin n)) (P : Fin n → Fin r)
    (hin : ∀ i, edgesIn G (part P i) ≤ a) (x : Fin n → ℝ)
    (hev : (G.adjMatrix ℝ).mulVec x = specRad G • x) (hx1 : ∀ j, x j ≤ 1)
    (hpos : ∀ j, 0 < x j) (z : Fin n) (hz : x z = 1) (i : Fin r) (hzi : P z = i) :
    specRad G ≤ (∑ q, (if P q ≠ i then x q else 0)) + a := by
  have hrow : ∑ q, (if G.Adj z q then x q else 0) = specRad G := by
    rw [← wk9_row G x z, hev]; simp [hz]
  have hcard := (wkx37_nbr_part_le G P z i hzi).trans (hin i)
  have h1 : ∀ q, (if G.Adj z q then x q else 0) ≤ (if P q ≠ i then x q else 0) +
      (if q ∈ G.neighborFinset z ∩ part P i then (1:ℝ) else 0) := by
    intro q
    by_cases hq : P q = i
    · rw [if_neg (not_not.2 hq), zero_add]
      by_cases ha : G.Adj z q
      · rw [if_pos ha, if_pos (Finset.mem_inter.2 ⟨(G.mem_neighborFinset z q).2 ha,
          (wkx_mem_part P _ q).2 hq⟩)]
        exact hx1 q
      · rw [if_neg ha]; split_ifs <;> norm_num
    · rw [if_pos hq]
      have : (0:ℝ) ≤ (if q ∈ G.neighborFinset z ∩ part P i then (1:ℝ) else 0) := by
        split_ifs <;> norm_num
      split_ifs <;> linarith [hpos q]
  have h2 := Finset.sum_le_sum (fun q (_ : q ∈ Finset.univ) => h1 q)
  rw [Finset.sum_add_distrib, Finset.sum_boole, Finset.filter_mem_eq_inter,
    Finset.univ_inter, hrow] at h2
  have h3 : (((G.neighborFinset z ∩ part P i).card : ℕ) : ℝ) ≤ a := by exact_mod_cast hcard
  linarith

open Classical Matrix in
theorem wkx38_lam {n : ℕ} (G : SimpleGraph (Fin n)) (hn : 0 < n) (d : ℝ)
    (hd : ∀ v, d < (G.degree v : ℝ)) : d < specRad G := by
  have hR := wkx37_rayleigh G hn (fun _ => 1)
  have hq : (fun _ : Fin n => (1:ℝ)) ⬝ᵥ (G.adjMatrix ℝ *ᵥ (fun _ => 1)) =
      ∑ v, (G.degree v : ℝ) := by
    simp [dotProduct, SimpleGraph.adjMatrix_mulVec_apply]
  have h11 : (fun _ : Fin n => (1:ℝ)) ⬝ᵥ (fun _ => 1) = n := by
    simp [dotProduct]
  rw [hq, h11] at hR
  have hne : (Finset.univ : Finset (Fin n)).Nonempty := ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  have hlt : ∑ _v : Fin n, d < ∑ v, (G.degree v : ℝ) :=
    Finset.sum_lt_sum_of_nonempty hne (fun v _ => hd v)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hlt
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  by_contra hcon
  push Not at hcon
  nlinarith [mul_le_mul_of_nonneg_left hcon hn'.le]

theorem wkx38_arith (L T xu a r n : ℝ) (ha : 1 ≤ a) (hr : 2 ≤ r) (hn : 0 < n)
    (hL : n / 4 ≤ L) (hK : T ≤ (L + 1) * xu) (hT : L ≤ T + a) :
    1 - 20 * a ^ 2 * r ^ 2 / n ≤ xu := by
  have hL1 : 0 < L + 1 := by
    have : 0 < n / 4 := by positivity
    linarith
  have hq : n / 4 * (20 * a ^ 2 * r ^ 2 / n) = 5 * a ^ 2 * r ^ 2 := by
    field_simp; ring
  have hqpos : 0 ≤ 20 * a ^ 2 * r ^ 2 / n := by positivity
  have h2 : n / 4 * (20 * a ^ 2 * r ^ 2 / n) ≤ (L + 1) * (20 * a ^ 2 * r ^ 2 / n) :=
    mul_le_mul_of_nonneg_right (by linarith) hqpos
  have ha2 : a + 1 ≤ 5 * a ^ 2 * r ^ 2 := by
    have e1 : a ≤ a ^ 2 := by nlinarith
    have e2 : 4 ≤ r ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left e2 (by positivity : (0:ℝ) ≤ a ^ 2)]
  have h3 : (L + 1) * (1 - 20 * a ^ 2 * r ^ 2 / n) ≤ (L + 1) * xu := by
    rw [mul_sub, mul_one]
    linarith
  exact le_of_mul_le_mul_left h3 hL1

open Classical in
theorem wkx38_core {W : Type*} [Fintype W] (F : SimpleGraph W) {n r a : ℕ} (hr : 2 ≤ r)
    (ha : 1 ≤ a) (G : SimpleGraph (Fin n)) (hG : IsSpectralExtremal F G) (P : Fin n → Fin r)
    (δ : ℝ) (hδ : 0 ≤ δ) (hδ4 : δ ≤ 1 / 4)
    (hdeg : ∀ v : Fin n, (1 - 1 / (r : ℝ) - δ) * n < (G.degree v : ℝ))
    (hin : ∀ i : Fin r, edgesIn G (part P i) ≤ a)
    (hbig : ((Fintype.card W : ℝ) + 2) * ((r : ℝ) * a + r * δ * n + 1) <
      (1 / (r : ℝ) - (r - 1) * δ) * n - (r - 1) * a)
    (x : Fin n → ℝ) (hev : (G.adjMatrix ℝ).mulVec x = specRad G • x)
    (hpos : ∀ j, 0 < x j) (hx1 : ∀ j, x j ≤ 1) (z : Fin n) (hz : x z = 1) (u : Fin n) :
    1 - 20 * (a : ℝ) ^ 2 * (r : ℝ) ^ 2 / n ≤ x u := by
  have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) u.isLt
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  have hr0 : (0:ℝ) < r := by exact_mod_cast (by omega : 0 < r)
  have hr2 : (2:ℝ) ≤ r := by exact_mod_cast hr
  have ha1 : (1:ℝ) ≤ a := by exact_mod_cast ha
  have hk0 : (0:ℝ) ≤ Fintype.card W := Nat.cast_nonneg _
  obtain ⟨i, hi⟩ : ∃ i, P z = i := ⟨_, rfl⟩
  have h37 := wkx37_core F hr G hG P δ hδ hdeg hin hbig i
  have hlow := wkx38_low hr G P δ hδ hdeg hin i
  have hsplit := Finset.card_filter_add_card_filter_not (s := part P i)
    (fun v => 1 ≤ ((G.neighborFinset v) ∩ part P i).card)
  have hfeq : (part P i).filter (fun v => ¬ (1 ≤ ((G.neighborFinset v) ∩ part P i).card)) =
      (part P i).filter (fun v => ((G.neighborFinset v) ∩ part P i).card = 0) :=
    Finset.filter_congr (fun v _ => by omega)
  rw [hfeq] at hsplit
  have hB := h37.1
  have hCcard : Fintype.card W + 2 ≤
      ((part P i).filter (fun v => ((G.neighborFinset v) ∩ part P i).card = 0)).card := by
    have hsplitR : ((((part P i).filter
        (fun v => 1 ≤ ((G.neighborFinset v) ∩ part P i).card)).card : ℕ) : ℝ) +
        (((part P i).filter (fun v => ((G.neighborFinset v) ∩ part P i).card = 0)).card : ℝ) =
        (part P i).card := by exact_mod_cast hsplit
    have hBR : ((((part P i).filter
        (fun v => 1 ≤ ((G.neighborFinset v) ∩ part P i).card)).card : ℕ) : ℝ) ≤ 2 * a := by
      exact_mod_cast hB
    have hext : ((Fintype.card W : ℝ) + 2) * ((r : ℝ) * a + r * δ * n + 1) ≥
        (Fintype.card W : ℝ) + 2 + 2 * a := by
      have h1 : (0:ℝ) ≤ r * δ * n := by positivity
      have hra : 2 * (a:ℝ) ≤ r * a := by nlinarith
      have h2 : (4:ℝ) * a ≤ ((Fintype.card W : ℝ) + 2) * (r * a) := by
        nlinarith [mul_nonneg hk0 (by positivity : (0:ℝ) ≤ r * a)]
      nlinarith
    have : (Fintype.card W : ℝ) + 2 <
        (((part P i).filter (fun v => ((G.neighborFinset v) ∩ part P i).card = 0)).card : ℝ) := by
      linarith
    exact_mod_cast this.le
  have hfree := wkx38_free F G hG.1 P u i _ hCcard
    (fun c hc w hw => h37.2 c hc w hw)
  have hle := hG.2 _ hfree
  have hK := wkx38_key G P u i hle x hev hpos
  have hT := wkx38_top G P hin x hev hx1 hpos z hz i hi
  have hL := wkx38_lam G hn _ hdeg
  have hL4 : (n:ℝ) / 4 ≤ specRad G := by
    have h1r : 1 / (r:ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hr2
    have : (n:ℝ) / 4 ≤ (1 - 1 / (r : ℝ) - δ) * n := by nlinarith
    linarith
  exact wkx38_arith (specRad G) _ (x u) a r n ha1 hr2 hn' hL4 hK hT

open Classical in
theorem wkx38_from36 {W : Type*} [Fintype W] (F : SimpleGraph W) (r a : ℕ) (hr : 2 ≤ r)
    (ha : 1 ≤ a)
    (h36 : ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ G : SimpleGraph (Fin n), IsSpectralExtremal F G →
        ∀ P : Fin n → Fin r, IsMaxCut G P →
          (∀ v : Fin n,
            (1 - 1 / (r : ℝ) - 3 * r * ε ^ ((1 : ℝ) / 3)) * n < (G.degree v : ℝ)) ∧
          ∀ i : Fin r, edgesIn G (part P i) ≤ a) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ G : SimpleGraph (Fin n), IsSpectralExtremal F G →
      ∀ x : Fin n → ℝ, (G.adjMatrix ℝ).mulVec x = specRad G • x →
        (∀ i, 0 < x i) → (∀ i, x i ≤ 1) → (∃ z, x z = 1) →
        ∀ u : Fin n, 1 - 20 * (a : ℝ) ^ 2 * (r : ℝ) ^ 2 / n ≤ x u := by
  obtain ⟨ε₀, hε₀, h⟩ := h36
  have hk0 : (0:ℝ) ≤ Fintype.card W := Nat.cast_nonneg _
  have hr0 : (0:ℝ) < r := by exact_mod_cast (by omega : 0 < r)
  have hr2 : (2:ℝ) ≤ r := by exact_mod_cast hr
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = 1 / (6 * (r:ℝ) ^ 3 * ((Fintype.card W : ℝ) + 3)) := ⟨_, rfl⟩
  have htpos : 0 < t := by rw [ht]; positivity
  obtain ⟨ε, hε⟩ : ∃ ε : ℝ, ε = min (ε₀ / 2) (t ^ 3) := ⟨_, rfl⟩
  have hεpos : 0 < ε := by rw [hε]; exact lt_min (by linarith) (by positivity)
  have hεlt : ε < ε₀ := by rw [hε]; exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hroot : ε ^ ((1:ℝ) / 3) ≤ t := by
    calc ε ^ ((1:ℝ) / 3) ≤ (t ^ 3) ^ ((1:ℝ) / 3) :=
          Real.rpow_le_rpow hεpos.le (by rw [hε]; exact min_le_right _ _) (by norm_num)
      _ = t := by
          rw [show ((1:ℝ) / 3) = ((3:ℕ):ℝ)⁻¹ by norm_num]
          exact Real.pow_rpow_inv_natCast htpos.le (by norm_num)
  have hδ0 : 0 ≤ 3 * (r:ℝ) * ε ^ ((1:ℝ) / 3) := by positivity
  have hδ' : ((Fintype.card W : ℝ) + 3) * r * (3 * (r:ℝ) * ε ^ ((1:ℝ) / 3)) ≤ 1 / (2 * r) := by
    calc ((Fintype.card W : ℝ) + 3) * r * (3 * (r:ℝ) * ε ^ ((1:ℝ) / 3))
        ≤ ((Fintype.card W : ℝ) + 3) * r * (3 * (r:ℝ) * t) := by gcongr
      _ = 1 / (2 * r) := by rw [ht]; field_simp; ring
  have hδ4 : 3 * (r:ℝ) * ε ^ ((1:ℝ) / 3) ≤ 1 / 4 := by
    have h1r : 1 / (2 * (r:ℝ)) ≤ 1 / 4 := one_div_le_one_div_of_le (by norm_num) (by linarith)
    have hkr : (6:ℝ) ≤ ((Fintype.card W : ℝ) + 3) * r := by nlinarith
    have := mul_le_mul_of_nonneg_right hkr hδ0
    linarith
  obtain ⟨n₀, hn₀⟩ := h ε hεpos hεlt
  obtain ⟨N1, hN1⟩ := exists_nat_ge
    (2 * (r:ℝ) * (((r:ℝ) - 1) * a + ((Fintype.card W : ℝ) + 2) * ((r:ℝ) * a + 1)) + 1)
  refine ⟨max n₀ N1, fun n hn G hG x hev hpos hx1 hz u => ?_⟩
  have : Nonempty (Fin r) := ⟨⟨0, by omega⟩⟩
  obtain ⟨P, hP⟩ := Finite.exists_max (fun P : Fin n → Fin r => crossEdges G P)
  obtain ⟨hdeg, hin⟩ := hn₀ n (le_of_max_le_left hn) G hG P hP
  have hnN : (N1 : ℝ) ≤ n := by exact_mod_cast le_of_max_le_right hn
  obtain ⟨z, hz⟩ := hz
  exact wkx38_core F hr ha G hG P _ hδ0 hδ4 hdeg hin
    (wkx37_arith r a (Fintype.card W) n _ hr2 hδ0 hk0 (Nat.cast_nonneg _) hδ'
      (hN1.trans hnN)) x hev hpos hx1 z hz u
end WKX37

open WangKangXue.SpectralTuran Classical in
-- Lemma 3.8 (Wang-Kang-Xue) by reduction to Lemma 3.6.
theorem solution {W : Type*} [Fintype W] (F : SimpleGraph W) (r a : ℕ) (hr : 2 ≤ r)
    (ha : 1 ≤ a) (hF : TuranPlusEdges F r a) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ G : SimpleGraph (Fin n), IsSpectralExtremal F G →
      ∀ x : Fin n → ℝ, (G.adjMatrix ℝ).mulVec x = specRad G • x →
        (∀ i, 0 < x i) → (∀ i, x i ≤ 1) → (∃ z, x z = 1) →
        ∀ u : Fin n, 1 - 20 * (a : ℝ) ^ 2 * (r : ℝ) ^ 2 / n ≤ x u := by
  exact wkx38_from36 F r a hr ha (lemma_3_6 F r a hr hF)
