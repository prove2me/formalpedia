-- Prove2me | solution 1 for WangKangXue.SpectralTuran.lemma_3_6
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-17T12:52:38.772868+00:00
-- url     : https://prove2.me/submissions/7229d8e8-5629-4910-8f4d-aeb7e0a5b349

import Mathlib
import Definitions.Def_WangKangXue_SpectralTuran_specRad
import Definitions.Def_WangKangXue_SpectralTuran_IsSpectralExtremal
import Definitions.Def_WangKangXue_SpectralTuran_TuranPlusEdges
import Definitions.Def_WangKangXue_SpectralTuran_edgesIn
import Definitions.Def_WangKangXue_SpectralTuran_IsMaxCut
import Theorems.Thm_WangKangXue_SpectralTuran_lemma_3_3
import Theorems.Thm_WangKangXue_SpectralTuran_lemma_3_1

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



section WKX6

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

def wkx39G {V : Type*} {r : ℕ} (G : SimpleGraph V) (B : Set V) (Q : V → Fin r) :
    SimpleGraph V where
  Adj u v := (u ∈ B ∧ v ∈ B ∧ G.Adj u v) ∨ (¬ (u ∈ B ∧ v ∈ B) ∧ Q u ≠ Q v)
  symm := ⟨fun u v h => by
    rcases h with ⟨h1, h2, h3⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨h2, h1, h3.symm⟩
    · exact Or.inr ⟨fun h => h1 ⟨h.2, h.1⟩, Ne.symm h2⟩⟩
  loopless := ⟨fun u h => by
    rcases h with ⟨-, -, h3⟩ | ⟨-, h2⟩
    · exact G.loopless.irrefl u h3
    · exact h2 rfl⟩


open Classical in
theorem wkx39_card {V : Type*} [Fintype V] (H K : SimpleGraph V) :
    (H.edgeFinset.card : ℤ) =
      K.edgeFinset.card + (H \ K).edgeFinset.card - (K \ H).edgeFinset.card := by
  have e1 : (H \ K).edgeFinset = H.edgeFinset \ K.edgeFinset := by
    ext e; simp
  have e2 : (K \ H).edgeFinset = K.edgeFinset \ H.edgeFinset := by
    ext e; simp
  rw [e1, e2]
  have h1 := Finset.card_sdiff_add_card_inter H.edgeFinset K.edgeFinset
  have h2 := Finset.card_sdiff_add_card_inter K.edgeFinset H.edgeFinset
  rw [Finset.inter_comm] at h2
  omega

open Classical in
theorem wkx39_in_le {n r : ℕ} (G : SimpleGraph (Fin n)) (P : Fin n → Fin r) :
    ∑ i, edgesIn G (part P i) ≤ (G \ completePartite P).edgeFinset.card := by
  unfold edgesIn
  rw [← Finset.card_biUnion]
  · apply Finset.card_le_card
    intro e he
    rw [Finset.mem_biUnion] at he
    obtain ⟨i, -, he⟩ := he
    simp only [Finset.mem_filter] at he
    obtain ⟨he, hall⟩ := he
    revert he hall
    refine Sym2.ind (fun x y => ?_) e
    intro he hall
    have hx : P x = i := (wkx_mem_part P i x).1 (hall x (Sym2.mem_mk_left x y))
    have hy : P y = i := (wkx_mem_part P i y).1 (hall y (Sym2.mem_mk_right x y))
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he ⊢
    refine ⟨he, ?_⟩
    change ¬ (P x ≠ P y)
    rw [hx, hy]
    exact not_not.2 rfl
  · intro i _ j _ hij
    rw [Function.onFun, Finset.disjoint_left]
    intro e hei hej
    simp only [Finset.mem_filter] at hei hej
    obtain ⟨x, hx⟩ : ∃ x, x ∈ e := by
      revert hei hej
      refine Sym2.ind (fun x y => ?_) e
      intro _ _
      exact ⟨x, Sym2.mem_mk_left x y⟩
    have h1 := (wkx_mem_part P i x).1 (hei.2 x hx)
    have h2 := (wkx_mem_part P j x).1 (hej.2 x hx)
    exact hij (h1.symm.trans h2)

theorem wkx39_sigma {n r : ℕ} (hr : 0 < r) (P : Fin n → Fin r) (B : Finset (Fin n)) (m : ℕ)
    (hB : ∀ i : Fin r, (B.filter (fun b => P b = i)).card ≤ m) (hn : r * m ≤ n) :
    ∃ σ : Fin n ≃ Fin n, ∀ b ∈ B, (σ b : ℕ) % r = P b := by
  classical
  let k : Fin n → ℕ := fun b => ((B.filter (fun c => P c = P b)).filter (fun c => c < b)).card
  have hk : ∀ b ∈ B, k b < m := by
    intro b hb
    have : k b < (B.filter (fun c => P c = P b)).card :=
      Finset.card_lt_card (Finset.filter_ssubset.2 ⟨b, by simp [hb], lt_irrefl b⟩)
    exact lt_of_lt_of_le this (hB _)
  have hlt : ∀ b ∈ B, (P b : ℕ) + r * k b < n := by
    intro b hb
    have h1 := hk b hb
    have h2 := (P b).isLt
    have : r * (k b + 1) ≤ r * m := Nat.mul_le_mul_left _ h1
    nlinarith
  let f : Fin n → Fin n := fun b => if h : (P b : ℕ) + r * k b < n then ⟨_, h⟩ else b
  have hf : ∀ b ∈ B, (f b : ℕ) = P b + r * k b := fun b hb => by
    simp only [f, dif_pos (hlt b hb)]
  have hmod : ∀ b ∈ B, (f b : ℕ) % r = P b := by
    intro b hb
    rw [hf b hb, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (P b).isLt]
  have hsub : ∀ b c, b ∈ B → c ∈ B → P b = P c → b < c → k b < k c := by
    intro b c hb hc hPbc hbc
    apply Finset.card_lt_card
    rw [Finset.ssubset_iff_of_subset]
    · exact ⟨b, by simp [hb, hPbc, hbc], by simp⟩
    · intro x hx
      simp only [Finset.mem_filter] at hx ⊢
      exact ⟨⟨hx.1.1, hx.1.2.trans hPbc⟩, hx.2.trans hbc⟩
  have hinj : Set.InjOn f B := by
    intro b hb c hc hbc
    have hb' : b ∈ B := hb
    have hc' : c ∈ B := hc
    have h := congrArg (fun x : Fin n => (x : ℕ)) hbc
    have hPbc : P b = P c := by
      apply Fin.ext
      rw [← hmod b hb', ← hmod c hc']
      exact congrArg (· % r) h
    rw [hf b hb', hf c hc', hPbc] at h
    have hkk : k b = k c := Nat.eq_of_mul_eq_mul_left hr (Nat.add_left_cancel h)
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt' | hlt'
    · have := hsub b c hb' hc' hPbc hlt'
      omega
    · have := hsub c b hc' hb' hPbc.symm hlt'
      omega
  obtain ⟨g, hg⟩ := Finset.exists_equiv_extend_of_card_eq
    (t := (Finset.univ : Finset (Fin n))) (by simp) (Finset.subset_univ _) hinj
  refine ⟨g.trans (Equiv.subtypeUnivEquiv Finset.mem_univ), fun b hb => ?_⟩
  have : ((g.trans (Equiv.subtypeUnivEquiv Finset.mem_univ)) b : Fin n) = f b := hg b hb
  rw [this]
  exact hmod b hb

theorem wkx39_iso {n r : ℕ} (hr : 0 < r) (σ : Fin n ≃ Fin n) :
    Nonempty (completePartite (fun v => (⟨(σ v : ℕ) % r, Nat.mod_lt _ hr⟩ : Fin r)) ≃g
      SimpleGraph.turanGraph n r) := by
  refine ⟨{ toEquiv := σ, map_rel_iff' := ?_ }⟩
  intro u v
  rw [SimpleGraph.turanGraph_adj]
  change _ ↔ (⟨(σ u : ℕ) % r, _⟩ : Fin r) ≠ ⟨(σ v : ℕ) % r, _⟩
  rw [Ne, Ne, Fin.mk.injEq]

theorem wkx39_cardeq {V : Type*} [Fintype V] (H1 H2 : SimpleGraph V) [i1 : Fintype H1.edgeSet]
    [i2 : Fintype H2.edgeSet] (h : H1 = H2) : H1.edgeFinset.card = H2.edgeFinset.card := by
  subst h; rw [Subsingleton.elim i1 i2]

open Classical in
theorem wkx10_in_le {n r : ℕ} (G : SimpleGraph (Fin n)) (P : Fin n → Fin r) :
    (G \ completePartite P).edgeFinset.card ≤ ∑ i, edgesIn G (part P i) := by
  unfold edgesIn
  refine le_trans (Finset.card_le_card ?_) Finset.card_biUnion_le
  intro e he
  induction e using Sym2.ind with
  | _ u w =>
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, SimpleGraph.sdiff_adj] at he
    have hP : P u = P w := by
      by_contra hc
      exact he.2 hc
    rw [Finset.mem_biUnion]
    refine ⟨P u, Finset.mem_univ _, ?_⟩
    rw [Finset.filter_congr_decidable, Finset.mem_filter]
    refine ⟨(SimpleGraph.mem_edgeFinset).2 he.1, ?_⟩
    intro v hv
    rw [Sym2.mem_iff] at hv
    rcases hv with rfl | rfl
    · exact (wkx_mem_part P _ _).2 rfl
    · exact (wkx_mem_part P _ _).2 hP.symm


open Classical in
theorem wkx6_hand {n : ℕ} (H : SimpleGraph (Fin n)) :
    ∑ v, (Finset.univ.filter (fun w => H.Adj v w)).card = 2 * H.edgeFinset.card := by
  rw [← SimpleGraph.sum_degrees_eq_twice_card_edges]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  congr 1
  ext w
  simp

theorem wkx6_count {n : ℕ} (f : Fin n → ℕ) (t : ℝ) :
    ((Finset.univ.filter (fun v => t ≤ (f v : ℝ))).card : ℝ) * t ≤ ∑ v, (f v : ℝ) := by
  classical
  calc ((Finset.univ.filter (fun v => t ≤ (f v : ℝ))).card : ℝ) * t
      = ∑ _v ∈ Finset.univ.filter (fun v => t ≤ (f v : ℝ)), t := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ v ∈ Finset.univ.filter (fun v => t ≤ (f v : ℝ)), (f v : ℝ) :=
        Finset.sum_le_sum (fun v hv => (Finset.mem_filter.1 hv).2)
    _ ≤ ∑ v, (f v : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun v _ _ => Nat.cast_nonneg _)

open Classical in
/-- number of neighbours of `v` in its own part -/
noncomputable def wkx6_own {n r : ℕ} (G : SimpleGraph (Fin n)) (P : Fin n → Fin r)
    (v : Fin n) : ℕ :=
  (Finset.univ.filter (fun w => G.Adj v w ∧ P w = P v)).card

open Classical in
/-- number of non-neighbours of `v` outside its own part -/
noncomputable def wkx6_miss {n r : ℕ} (G : SimpleGraph (Fin n)) (P : Fin n → Fin r)
    (v : Fin n) : ℕ :=
  (Finset.univ.filter (fun w => P w ≠ P v ∧ ¬ G.Adj v w)).card

open Classical in
theorem wkx6_sum_own {n r : ℕ} (G : SimpleGraph (Fin n)) (P : Fin n → Fin r) :
    ∑ v, wkx6_own G P v = 2 * (G \ completePartite P).edgeFinset.card := by
  refine Eq.trans ?_ (by convert wkx6_hand (G \ completePartite P))
  refine Finset.sum_congr rfl (fun v _ => ?_)
  unfold wkx6_own
  congr 1
  ext w
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, SimpleGraph.sdiff_adj]
  change _ ↔ G.Adj v w ∧ ¬ (P v ≠ P w)
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, fun h => h h2.symm⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, (not_not.1 h2).symm⟩

open Classical in
theorem wkx6_sum_miss {n r : ℕ} (G : SimpleGraph (Fin n)) (P : Fin n → Fin r) :
    ∑ v, wkx6_miss G P v = 2 * (completePartite P \ G).edgeFinset.card := by
  refine Eq.trans ?_ (by convert wkx6_hand (completePartite P \ G))
  refine Finset.sum_congr rfl (fun v _ => ?_)
  unfold wkx6_miss
  congr 1
  ext w
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, SimpleGraph.sdiff_adj]
  change _ ↔ P v ≠ P w ∧ ¬ G.Adj v w
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨Ne.symm h1, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨Ne.symm h1, h2⟩

open Classical in
theorem wkx6_deg_eq {n r : ℕ} (G : SimpleGraph (Fin n)) (P : Fin n → Fin r) (v : Fin n) :
    G.degree v + wkx6_miss G P v + (part P (P v)).card = wkx6_own G P v + n := by
  unfold wkx6_miss wkx6_own
  have e1 := Finset.card_filter_add_card_filter_not (s := Finset.univ.filter (G.Adj v))
    (fun w => P w = P v)
  have e2 := Finset.card_filter_add_card_filter_not
    (s := Finset.univ.filter (fun w => P w ≠ P v)) (fun w => G.Adj v w)
  have e3 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
    (fun w => P w = P v)
  rw [Finset.filter_filter, Finset.filter_filter] at e1 e2
  rw [Finset.card_univ, Fintype.card_fin] at e3
  have hd : G.degree v = (Finset.univ.filter (G.Adj v)).card := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    congr 1; ext w; simp
  have hp : (part P (P v)).card = (Finset.univ.filter (fun w => P w = P v)).card := by
    congr 1
  have q1 : (Finset.univ.filter (fun w => P w ≠ P v ∧ G.Adj v w)).card =
      (Finset.univ.filter (fun w => G.Adj v w ∧ ¬ P w = P v)).card := by
    congr 1; ext w; simp [and_comm]
  have q2 : (Finset.univ.filter (fun w => ¬ P w = P v)).card =
      (Finset.univ.filter (fun w => P w ≠ P v)).card := rfl
  omega

theorem wkx6_KP_le {n r : ℕ} (P : Fin n → Fin r) [DecidableRel (completePartite P).Adj] :
    (completePartite P).edgeFinset.card ≤ (SimpleGraph.turanGraph n r).edgeFinset.card := by
  have hc : (completePartite P).Colorable r := ⟨SimpleGraph.Coloring.mk P (fun h => h)⟩
  have hcf : (completePartite P).CliqueFree (r + 1) := hc.cliqueFree (Nat.lt_succ_self r)
  have h1 := SimpleGraph.CliqueFree.card_edgeFinset_le hcf
  dsimp only at h1
  rw [Fintype.card_fin] at h1
  rw [SimpleGraph.card_edgeFinset_turanGraph]
  exact h1

open Classical in
theorem wkx6_KPG0 {V : Type*} [Fintype V] (G K : SimpleGraph V) (t s : ℕ) (ε N2 : ℝ)
    (h1 : (t : ℝ) - ε * N2 ≤ G.edgeFinset.card) (h2 : (s : ℝ) ≤ ε * N2)
    (hin : (G \ K).edgeFinset.card ≤ s) (hK : K.edgeFinset.card ≤ t) :
    ((K \ G).edgeFinset.card : ℝ) ≤ 2 * ε * N2 := by
  have hc := wkx39_card G K
  have hc' : ((G.edgeFinset.card : ℤ) : ℝ) = (((K.edgeFinset.card : ℤ) +
      ((G \ K).edgeFinset.card : ℤ) - ((K \ G).edgeFinset.card : ℤ) : ℤ) : ℝ) := by rw [hc]
  push_cast at hc'
  have h3 : ((G \ K).edgeFinset.card : ℝ) ≤ s := by exact_mod_cast hin
  have h4 : (K.edgeFinset.card : ℝ) ≤ t := by exact_mod_cast hK
  linarith

open Classical in
theorem wkx6_KPG {n r : ℕ} (G : SimpleGraph (Fin n)) (P : Fin n → Fin r) (ε : ℝ)
    (h1 : ((SimpleGraph.turanGraph n r).edgeFinset.card : ℝ) - ε * (n : ℝ) ^ 2 ≤
      G.edgeFinset.card)
    (h2 : ((∑ i, edgesIn G (part P i) : ℕ) : ℝ) ≤ ε * (n : ℝ) ^ 2) :
    ((completePartite P \ G).edgeFinset.card : ℝ) ≤ 2 * ε * (n : ℝ) ^ 2 := by
  convert wkx6_KPG0 G (completePartite P) (SimpleGraph.turanGraph n r).edgeFinset.card
    (∑ i, edgesIn G (part P i)) ε ((n:ℝ)^2) h1 h2 (by convert wkx10_in_le G P)
    (by convert wkx6_KP_le P) using 3
  ext e
  simp

open Classical in
theorem wkx6_rowcmp {n : ℕ} (H0 H1 : SimpleGraph (Fin n)) (v : Fin n)
    (hagree : ∀ p q, p ≠ v → q ≠ v → (H1.Adj p q ↔ H0.Adj p q))
    (hle : H1.edgeFinset.card ≤ H0.edgeFinset.card) (p0 p1 : Fin n → Prop)
    [DecidablePred p0] [DecidablePred p1]
    (h0 : ∀ w, H0.Adj v w ↔ p0 w) (h1 : ∀ w, H1.Adj v w ↔ p1 w) :
    (Finset.univ.filter p1).card ≤ (Finset.univ.filter p0).card := by
  have hq := wkx38_quad_diff H0 H1 v hagree (fun _ => 1)
  simp only [mul_one, Finset.sum_boole] at hq
  have hA := wkx6_hand H1
  have hB := wkx6_hand H0
  have hA' : ((∑ v, (Finset.univ.filter (fun w => H1.Adj v w)).card : ℕ) : ℝ) =
      2 * (H1.edgeFinset.card : ℝ) := by exact_mod_cast hA
  have hB' : ((∑ v, (Finset.univ.filter (fun w => H0.Adj v w)).card : ℕ) : ℝ) =
      2 * (H0.edgeFinset.card : ℝ) := by exact_mod_cast hB
  push_cast at hA' hB'
  have hle' : (H1.edgeFinset.card : ℝ) ≤ H0.edgeFinset.card := by exact_mod_cast hle
  have key : ((Finset.univ.filter (fun w => H1.Adj v w)).card : ℝ) ≤
      (Finset.univ.filter (fun w => H0.Adj v w)).card := by linarith
  have e0 : (Finset.univ.filter p0) = Finset.univ.filter (fun w => H0.Adj v w) := by
    ext w; simp [h0]
  have e1 : (Finset.univ.filter p1) = Finset.univ.filter (fun w => H1.Adj v w) := by
    ext w; simp [h1]
  rw [e0, e1]
  exact_mod_cast key

open Classical in
theorem wkx6_maxcut {n r : ℕ} (G : SimpleGraph (Fin n)) (P : Fin n → Fin r)
    (hP : IsMaxCut G P) (v : Fin n) (j : Fin r) :
    wkx6_own G P v ≤ (Finset.univ.filter (fun w => G.Adj v w ∧ P w = j)).card := by
  obtain ⟨P', hP'⟩ : ∃ P', P' = Function.update P v j := ⟨_, rfl⟩
  have hle := hP P'
  unfold crossEdges at hle
  have hrow := wkx6_rowcmp (G ⊓ completePartite P) (G ⊓ completePartite P') v
    (fun p q hp hq => by
      simp only [SimpleGraph.inf_adj]
      change (G.Adj p q ∧ P' p ≠ P' q) ↔ (G.Adj p q ∧ P p ≠ P q)
      rw [hP', Function.update_of_ne hp, Function.update_of_ne hq]) (by convert hle)
    (fun w => G.Adj v w ∧ ¬ P w = P v) (fun w => G.Adj v w ∧ ¬ P w = j)
    (fun w => by
      simp only [SimpleGraph.inf_adj]
      change (G.Adj v w ∧ P v ≠ P w) ↔ _
      exact ⟨fun h => ⟨h.1, fun e => h.2 e.symm⟩, fun h => ⟨h.1, fun e => h.2 e.symm⟩⟩)
    (fun w => by
      simp only [SimpleGraph.inf_adj]
      change (G.Adj v w ∧ P' v ≠ P' w) ↔ _
      constructor
      · rintro ⟨h1, h2⟩
        have hw : w ≠ v := fun h => G.loopless.irrefl v (h ▸ h1)
        rw [hP', Function.update_self, Function.update_of_ne hw] at h2
        exact ⟨h1, fun h => h2 h.symm⟩
      · rintro ⟨h1, h2⟩
        have hw : w ≠ v := fun h => G.loopless.irrefl v (h ▸ h1)
        rw [hP', Function.update_self, Function.update_of_ne hw]
        exact ⟨h1, fun h => h2 h.symm⟩)
  have e1 := Finset.card_filter_add_card_filter_not (s := Finset.univ.filter (G.Adj v))
    (fun w => P w = P v)
  have e2 := Finset.card_filter_add_card_filter_not (s := Finset.univ.filter (G.Adj v))
    (fun w => P w = j)
  rw [Finset.filter_filter, Finset.filter_filter] at e1 e2
  unfold wkx6_own
  omega

theorem wkx6_emb {W : Type*} [Fintype W] (F : SimpleGraph W) {n r : ℕ}
    (G : SimpleGraph (Fin n)) (hG : F.Free G) (B : Finset (Fin n)) (P Q : Fin n → Fin r)
    (hQ : ∀ b ∈ B, Q b = P b) (D : Finset (Fin n))
    (hc : ∀ j : Fin r, ∀ X : Finset (Fin n), X ⊆ D → X.card ≤ Fintype.card W →
      ∃ c ∈ D, P c = j ∧ c ∉ X ∧ c ∉ B ∧ (∀ x ∈ X, P x ≠ j → G.Adj x c) ∧
        (∀ b ∈ B, P b ≠ j → G.Adj b c)) :
    F.Free (wkx39G G (B : Set (Fin n)) Q) := by
  classical
  rintro ⟨f⟩
  apply hG
  have key : ∀ U : Finset W, ∃ g : W → Fin n,
      (∀ p, f.toHom p ∈ B → g p = f.toHom p) ∧
      (∀ p ∈ U, f.toHom p ∉ B → g p ∈ D ∧ g p ∉ B ∧ P (g p) = Q (f.toHom p) ∧
          ∀ b ∈ B, P b ≠ Q (f.toHom p) → G.Adj b (g p)) ∧
      (∀ p ∈ U, ∀ q ∈ U, f.toHom p ∉ B → f.toHom q ∉ B → p ≠ q →
          g p ≠ g q ∧ (Q (f.toHom p) ≠ Q (f.toHom q) → G.Adj (g p) (g q))) := by
    intro U
    induction U using Finset.induction_on with
    | empty => exact ⟨f.toHom, fun _ _ => rfl, by simp, by simp⟩
    | insert p U hpU ih =>
      obtain ⟨g, hg1, hg2, hg3⟩ := ih
      by_cases hpB : f.toHom p ∈ B
      · refine ⟨g, hg1, ?_, ?_⟩
        · intro q hq hqB
          rcases Finset.mem_insert.1 hq with hq0 | hq
          · rw [hq0] at hqB; exact absurd hpB hqB
          · exact hg2 q hq hqB
        · intro q hq s hs hqB hsB hqs
          rcases Finset.mem_insert.1 hq with hq0 | hq
          · rw [hq0] at hqB; exact absurd hpB hqB
          rcases Finset.mem_insert.1 hs with hs0 | hs
          · rw [hs0] at hsB; exact absurd hpB hsB
          exact hg3 q hq s hs hqB hsB hqs
      · obtain ⟨X, hX⟩ : ∃ X, X = (U.filter (fun q => f.toHom q ∉ B)).image g := ⟨_, rfl⟩
        have hmemX : ∀ t ∈ U, f.toHom t ∉ B → g t ∈ X := fun t ht htB => by
          rw [hX]; exact Finset.mem_image_of_mem g (Finset.mem_filter.2 ⟨ht, htB⟩)
        have hXD : X ⊆ D := by
          intro x hx
          rw [hX] at hx
          obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hx
          rw [Finset.mem_filter] at hq
          exact (hg2 q hq.1 hq.2).1
        have hXc : X.card ≤ Fintype.card W := by
          rw [hX]
          exact Finset.card_image_le.trans (Finset.card_le_univ _)
        obtain ⟨c, hcD, hcP, hcX, hcB, hcadj, hcbadj⟩ := hc (Q (f.toHom p)) X hXD hXc
        refine ⟨Function.update g p c, ?_, ?_, ?_⟩
        · intro q hq
          have : q ≠ p := fun h => hpB (h ▸ hq)
          rw [Function.update_of_ne this]; exact hg1 q hq
        · intro q hq hqB
          rcases Finset.mem_insert.1 hq with hq0 | hq
          · rw [hq0, Function.update_self]; exact ⟨hcD, hcB, hcP, hcbadj⟩
          · have : q ≠ p := fun h => hpU (h ▸ hq)
            rw [Function.update_of_ne this]; exact hg2 q hq hqB
        · intro q hq s hs hqB hsB hqs
          rcases Finset.mem_insert.1 hq with hq0 | hq' <;>
            rcases Finset.mem_insert.1 hs with hs0 | hs'
          · exact absurd (hq0.trans hs0.symm) hqs
          · have hsp : s ≠ p := fun h => hpU (h ▸ hs')
            rw [hq0, Function.update_self, Function.update_of_ne hsp]
            have hgs := hg2 s hs' hsB
            refine ⟨fun h => hcX (h ▸ hmemX s hs' hsB), fun hne => ?_⟩
            exact (hcadj _ (hmemX s hs' hsB) (by rw [hgs.2.2.1]; exact Ne.symm hne)).symm
          · have hqp : q ≠ p := fun h => hpU (h ▸ hq')
            rw [hs0, Function.update_self, Function.update_of_ne hqp]
            have hgq := hg2 q hq' hqB
            refine ⟨fun h => hcX (h ▸ hmemX q hq' hqB), fun hne => ?_⟩
            exact hcadj _ (hmemX q hq' hqB) (by rw [hgq.2.2.1]; exact hne)
          · have hqp : q ≠ p := fun h => hpU (h ▸ hq')
            have hsp : s ≠ p := fun h => hpU (h ▸ hs')
            rw [Function.update_of_ne hqp, Function.update_of_ne hsp]
            exact hg3 q hq' s hs' hqB hsB hqs
  obtain ⟨g, hg1, hg2, hg3⟩ := key Finset.univ
  refine ⟨⟨⟨g, ?_⟩, ?_⟩⟩
  · intro p q hpq
    have hf : (wkx39G G (B : Set (Fin n)) Q).Adj (f.toHom p) (f.toHom q) :=
      f.toHom.map_adj hpq
    by_cases hp : f.toHom p ∈ B <;> by_cases hq : f.toHom q ∈ B
    · rcases hf with ⟨-, -, h⟩ | ⟨hnb, -⟩
      · rw [hg1 p hp, hg1 q hq]; exact h
      · exact (hnb ⟨hp, hq⟩).elim
    · rcases hf with ⟨-, h, -⟩ | ⟨-, hne⟩
      · exact absurd h hq
      · have hgq := hg2 q (Finset.mem_univ _) hq
        rw [hg1 p hp]
        exact hgq.2.2.2 _ hp (by rw [← hQ _ hp]; exact hne)
    · rcases hf with ⟨h, -, -⟩ | ⟨-, hne⟩
      · exact absurd h hp
      · have hgp := hg2 p (Finset.mem_univ _) hp
        rw [hg1 q hq]
        exact (hgp.2.2.2 _ hq (by rw [← hQ _ hq]; exact Ne.symm hne)).symm
    · rcases hf with ⟨h, -, -⟩ | ⟨-, hne⟩
      · exact absurd h hp
      · exact (hg3 p (Finset.mem_univ _) q (Finset.mem_univ _) hp hq (F.ne_of_adj hpq)).2 hne
  · intro p q hpq
    change g p = g q at hpq
    by_contra hne
    by_cases hp : f.toHom p ∈ B <;> by_cases hq : f.toHom q ∈ B
    · rw [hg1 p hp, hg1 q hq] at hpq; exact hne (f.injective hpq)
    · have := (hg2 q (Finset.mem_univ _) hq).2.1
      rw [← hpq, hg1 p hp] at this; exact this hp
    · have := (hg2 p (Finset.mem_univ _) hp).2.1
      rw [hpq, hg1 q hq] at this; exact this hq
    · exact (hg3 p (Finset.mem_univ _) q (Finset.mem_univ _) hp hq hne).1 hpq

open Classical in
theorem wkx6_cnt {V : Type*} [Fintype V] (H K : SimpleGraph V) (T : Finset (Sym2 V)) (t a : ℕ)
    (h0 : (K \ H).edgeFinset.card = 0) (h1 : T.card ≤ (H \ K).edgeFinset.card)
    (h2 : H.edgeFinset.card ≤ t + a) (h3 : K.edgeFinset.card = t) (hT : a + 1 ≤ T.card) :
    False := by
  have hc := wkx39_card H K
  omega

open Classical in
theorem wkx6_edgecore {W : Type*} [Fintype W] (F : SimpleGraph W) {n r a : ℕ} (hr : 0 < r)
    (G : SimpleGraph (Fin n)) (hG : F.Free G) (P : Fin n → Fin r)
    (hext : SimpleGraph.extremalNumber n F = (SimpleGraph.turanGraph n r).edgeFinset.card + a)
    (i : Fin r) (B : Finset (Fin n)) (hBi : ∀ b ∈ B, P b = i) (hBn : r * B.card ≤ n)
    (T : Finset (Sym2 (Fin n))) (hT : ∀ e ∈ T, e ∈ G.edgeSet ∧ ∀ v ∈ e, v ∈ B)
    (hTa : a + 1 ≤ T.card) (D : Finset (Fin n))
    (hc : ∀ j : Fin r, ∀ X : Finset (Fin n), X ⊆ D → X.card ≤ Fintype.card W →
      ∃ c ∈ D, P c = j ∧ c ∉ X ∧ c ∉ B ∧ (∀ x ∈ X, P x ≠ j → G.Adj x c) ∧
        (∀ b ∈ B, P b ≠ j → G.Adj b c)) : False := by
  obtain ⟨σ, hσ⟩ := wkx39_sigma hr P B B.card (fun j => Finset.card_filter_le _ _) hBn
  obtain ⟨Q, hQd⟩ : ∃ Q : Fin n → Fin r, Q = fun v => ⟨(σ v : ℕ) % r, Nat.mod_lt _ hr⟩ :=
    ⟨_, rfl⟩
  have hQ : ∀ b ∈ B, Q b = P b := fun b hb => by rw [hQd]; exact Fin.ext (hσ b hb)
  have hfree := wkx6_emb F G hG B P Q hQ D hc
  have hle := SimpleGraph.card_edgeFinset_le_extremalNumber hfree
  rw [Fintype.card_fin, hext] at hle
  obtain ⟨e⟩ := wkx39_iso hr σ
  rw [← hQd] at e
  have hKT : (completePartite Q).edgeFinset.card =
      (SimpleGraph.turanGraph n r).edgeFinset.card := by
    convert e.card_edgeFinset_eq
  have hc' := wkx39_card (wkx39G G (B : Set (Fin n)) Q) (completePartite Q)
  have hKH : (completePartite Q \ wkx39G G (B : Set (Fin n)) Q).edgeFinset.card = 0 := by
    rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro e he
    induction e using Sym2.ind with
    | _ u w =>
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, SimpleGraph.sdiff_adj] at he
      obtain ⟨h1, h2⟩ := he
      apply h2
      by_cases hu : u ∈ B
      · by_cases hw : w ∈ B
        · exfalso; apply h1; rw [hQ u hu, hQ w hw, hBi u hu, hBi w hw]
        · exact Or.inr ⟨fun h => hw h.2, h1⟩
      · exact Or.inr ⟨fun h => hu h.1, h1⟩
  have hHK : T.card ≤ (wkx39G G (B : Set (Fin n)) Q \ completePartite Q).edgeFinset.card := by
    apply Finset.card_le_card
    intro e he
    obtain ⟨heG, heB⟩ := hT e he
    revert heG heB
    induction e using Sym2.ind with
    | _ u w =>
      intro heG heB
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, SimpleGraph.sdiff_adj]
      have hu := heB u (Sym2.mem_mk_left u w)
      have hw := heB w (Sym2.mem_mk_right u w)
      refine ⟨Or.inl ⟨hu, hw, heG⟩, ?_⟩
      change ¬ (Q u ≠ Q w)
      rw [hQ u hu, hQ w hw, hBi u hu, hBi w hw]; exact not_not.2 rfl
  exact wkx6_cnt (wkx39G G (B : Set (Fin n)) Q) (completePartite Q) T
    (SimpleGraph.turanGraph n r).edgeFinset.card a (by convert hKH) (by convert hHK)
    (by convert hle) (by convert hKT) hTa

open Classical in
theorem wkx6_find {n : ℕ} (G : SimpleGraph (Fin n)) (A S X : Finset (Fin n)) (M : ℝ)
    (hM : ∀ y ∈ S, ((A \ G.neighborFinset y).card : ℝ) ≤ M)
    (hbig : (X.card : ℝ) + S.card * M < A.card) :
    ∃ c ∈ A, c ∉ X ∧ ∀ y ∈ S, G.Adj y c := by
  have e1 : (X ∪ S.biUnion (fun y => A \ G.neighborFinset y)).card ≤
      X.card + (S.biUnion (fun y => A \ G.neighborFinset y)).card :=
    Finset.card_union_le _ _
  have e2 : (S.biUnion (fun y => A \ G.neighborFinset y)).card ≤
      ∑ y ∈ S, (A \ G.neighborFinset y).card := Finset.card_biUnion_le
  have e3 : ((∑ y ∈ S, (A \ G.neighborFinset y).card : ℕ) : ℝ) ≤ S.card * M := by
    push_cast
    calc ∑ y ∈ S, ((A \ G.neighborFinset y).card : ℝ) ≤ ∑ _y ∈ S, M :=
          Finset.sum_le_sum (fun y hy => hM y hy)
      _ = S.card * M := by rw [Finset.sum_const, nsmul_eq_mul]
  have e4 : ((X ∪ S.biUnion (fun y => A \ G.neighborFinset y)).card : ℝ) ≤
      X.card + ((∑ y ∈ S, (A \ G.neighborFinset y).card : ℕ) : ℝ) := by
    exact_mod_cast e1.trans (Nat.add_le_add_left e2 _)
  have hlt : (X ∪ S.biUnion (fun y => A \ G.neighborFinset y)).card < A.card := by
    have : ((X ∪ S.biUnion (fun y => A \ G.neighborFinset y)).card : ℝ) < A.card := by
      linarith
    exact_mod_cast this
  obtain ⟨c, hc, hcb⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  refine ⟨c, hc, fun h => hcb (Finset.mem_union_left _ h), fun y hy => ?_⟩
  by_contra hna
  apply hcb
  refine Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨y, hy, ?_⟩)
  rw [Finset.mem_sdiff, SimpleGraph.mem_neighborFinset]
  exact ⟨hc, hna⟩

open Classical in
theorem wkx6_part_miss {n r : ℕ} (G : SimpleGraph (Fin n)) (P : Fin n → Fin r) (y : Fin n)
    (j : Fin r) (hj : P y ≠ j) (A : Finset (Fin n)) (hA : A ⊆ part P j) :
    (A \ G.neighborFinset y).card ≤ wkx6_miss G P y := by
  unfold wkx6_miss
  apply Finset.card_le_card
  intro w hw
  rw [Finset.mem_sdiff, SimpleGraph.mem_neighborFinset] at hw
  have hPw : P w = j := (wkx_mem_part P j w).1 (hA hw.1)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨by rw [hPw]; exact Ne.symm hj, hw.2⟩

open Classical in
theorem wkx6_hc {n r : ℕ} (G : SimpleGraph (Fin n)) (P : Fin n → Fin r) (D B : Finset (Fin n))
    (k : ℕ) (M : ℝ) (hM0 : 0 ≤ M)
    (hD : ∀ y ∈ D, (wkx6_miss G P y : ℝ) ≤ M)
    (hpool : ∀ j : Fin r, ∃ A : Finset (Fin n), A ⊆ part P j ∩ D ∧
      ∃ S0 : Finset (Fin n), S0 ⊆ D ∧
        (∀ b ∈ B, P b ≠ j → b ∈ S0 ∨ ∀ c ∈ A, G.Adj b c) ∧
        ((k + B.card : ℕ) : ℝ) + ((k + S0.card : ℕ) : ℝ) * M < A.card) :
    ∀ j : Fin r, ∀ X : Finset (Fin n), X ⊆ D → X.card ≤ k →
      ∃ c ∈ D, P c = j ∧ c ∉ X ∧ c ∉ B ∧ (∀ x ∈ X, P x ≠ j → G.Adj x c) ∧
        (∀ b ∈ B, P b ≠ j → G.Adj b c) := by
  intro j X hXD hXk
  obtain ⟨A, hA, S0, hS0, hB, hbig⟩ := hpool j
  have hApart : A ⊆ part P j := fun x hx => (Finset.mem_inter.1 (hA hx)).1
  obtain ⟨c, hcA, hcX, hcadj⟩ := wkx6_find G A ((X ∪ S0).filter (fun y => P y ≠ j)) (X ∪ B) M
    (fun y hy => by
      rw [Finset.mem_filter] at hy
      have hyD : y ∈ D := by
        rcases Finset.mem_union.1 hy.1 with h | h
        · exact hXD h
        · exact hS0 h
      exact le_trans (by exact_mod_cast wkx6_part_miss G P y j hy.2 A hApart) (hD y hyD))
    (by
      have h1 : ((X ∪ B).card : ℝ) ≤ ((k + B.card : ℕ) : ℝ) := by
        exact_mod_cast (Finset.card_union_le _ _).trans (Nat.add_le_add_right hXk _)
      have h2 : (((X ∪ S0).filter (fun y => P y ≠ j)).card : ℝ) ≤ ((k + S0.card : ℕ) : ℝ) := by
        exact_mod_cast (Finset.card_filter_le _ _).trans
          ((Finset.card_union_le _ _).trans (Nat.add_le_add_right hXk _))
      have h3 := mul_le_mul_of_nonneg_right h2 hM0
      linarith)
  have hcAD := Finset.mem_inter.1 (hA hcA)
  refine ⟨c, hcAD.2, (wkx_mem_part P j c).1 hcAD.1, fun h => hcX (Finset.mem_union_left _ h),
    fun h => hcX (Finset.mem_union_right _ h), fun x hx hxj => ?_, fun b hb hbj => ?_⟩
  · exact hcadj x (Finset.mem_filter.2 ⟨Finset.mem_union_left _ hx, hxj⟩)
  · rcases hB b hb hbj with h | h
    · exact hcadj b (Finset.mem_filter.2 ⟨Finset.mem_union_right _ h, hbj⟩)
    · exact h c hcA

theorem wkx6_inter_card {n : ℕ} (S D : Finset (Fin n)) :
    (S.card : ℝ) - ((Finset.univ \ D).card : ℝ) ≤ (S ∩ D).card := by
  classical
  have h : S ⊆ (S ∩ D) ∪ (Finset.univ \ D) := by
    intro x hx
    by_cases hd : x ∈ D
    · exact Finset.mem_union_left _ (Finset.mem_inter.2 ⟨hx, hd⟩)
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.2 ⟨Finset.mem_univ _, hd⟩)
  have := (Finset.card_le_card h).trans (Finset.card_union_le _ _)
  have : (S.card : ℝ) ≤ (S ∩ D).card + (Finset.univ \ D).card := by exact_mod_cast this
  linarith

open Classical in
theorem wkx6_vcard {n : ℕ} (T : Finset (Sym2 (Fin n))) :
    (Finset.univ.filter (fun v => ∃ e ∈ T, v ∈ e)).card ≤ 2 * T.card := by
  have hsub : Finset.univ.filter (fun v => ∃ e ∈ T, v ∈ e) ⊆
      T.biUnion (fun e => Finset.univ.filter (fun v => v ∈ e)) := by
    intro v hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
    obtain ⟨e, he, hve⟩ := hv
    exact Finset.mem_biUnion.2 ⟨e, he, by simp [hve]⟩
  refine (Finset.card_le_card hsub).trans (Finset.card_biUnion_le.trans ?_)
  rw [mul_comm, ← smul_eq_mul, ← Finset.sum_const]
  refine Finset.sum_le_sum (fun e _ => ?_)
  induction e using Sym2.ind with
  | _ p q =>
    refine le_trans (Finset.card_le_card (t := ({p, q} : Finset (Fin n))) ?_) Finset.card_le_two
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Sym2.mem_iff] at hx
    rcases hx with rfl | rfl <;> simp

open Classical in
theorem wkx6_stepC {W : Type*} [Fintype W] (F : SimpleGraph W) {n r a : ℕ} (hr : 0 < r)
    (G : SimpleGraph (Fin n)) (hG : F.Free G) (P : Fin n → Fin r) (hP : IsMaxCut G P)
    (hext : SimpleGraph.extremalNumber n F = (SimpleGraph.turanGraph n r).edgeFinset.card + a)
    (D : Finset (Fin n)) (M β s0 : ℝ) (hM0 : 0 ≤ M)
    (hD : ∀ y ∈ D, (wkx6_miss G P y : ℝ) ≤ M)
    (hDc : ((Finset.univ \ D).card : ℝ) ≤ β)
    (hs0 : ∀ j, s0 ≤ (part P j).card)
    (hn : r * (a + 2) ≤ n) (v : Fin n) (t : ℝ)
    (hown : t ≤ wkx6_own G P v)
    (hbig1 : ((Fintype.card W + (a + 2) : ℕ) : ℝ) + ((Fintype.card W + (a + 1) : ℕ) : ℝ) * M <
      t - β)
    (hbig2 : ((Fintype.card W + (a + 2) : ℕ) : ℝ) + ((Fintype.card W + 0 : ℕ) : ℝ) * M <
      s0 - β) :
    False := by
  have hk0 : (0:ℝ) ≤ ((Fintype.card W + (a + 1) : ℕ) : ℝ) * M := by positivity
  -- leaves
  obtain ⟨Li, hLi⟩ : ∃ Li : Finset (Fin n),
      Li = Finset.univ.filter (fun w => G.Adj v w ∧ P w = P v) ∩ D := ⟨_, rfl⟩
  have hLic : (a + 1 : ℝ) ≤ Li.card := by
    have h1 := wkx6_inter_card (Finset.univ.filter (fun w => G.Adj v w ∧ P w = P v)) D
    rw [← hLi] at h1
    have h2 : (wkx6_own G P v : ℝ) = (Finset.univ.filter (fun w => G.Adj v w ∧ P w = P v)).card :=
      rfl
    have h3 : ((Fintype.card W + (a + 2) : ℕ) : ℝ) ≥ a + 1 := by push_cast; linarith
    linarith
  obtain ⟨L, hLsub, hLcard⟩ := Finset.exists_subset_card_eq
    (show a + 1 ≤ Li.card by exact_mod_cast hLic)
  have hLmem : ∀ l ∈ L, G.Adj v l ∧ P l = P v ∧ l ∈ D := by
    intro l hl
    have := hLsub hl
    rw [hLi, Finset.mem_inter, Finset.mem_filter] at this
    exact ⟨this.1.2.1, this.1.2.2, this.2⟩
  have hvL : v ∉ L := fun h => G.loopless.irrefl v (hLmem v h).1
  obtain ⟨B, hB⟩ : ∃ B : Finset (Fin n), B = insert v L := ⟨_, rfl⟩
  have hBcard : B.card = a + 2 := by rw [hB, Finset.card_insert_of_notMem hvL, hLcard]
  have hBi : ∀ b ∈ B, P b = P v := by
    intro b hb
    rw [hB, Finset.mem_insert] at hb
    rcases hb with rfl | hb
    · rfl
    · exact (hLmem b hb).2.1
  have hinj : Function.Injective (fun y : Fin n => s(v, y)) := by
    intro y1 y2 h
    rcases Sym2.eq_iff.1 h with ⟨_, h⟩ | h
    · exact h
    · exact h.2.trans h.1
  obtain ⟨T, hT⟩ : ∃ T : Finset (Sym2 (Fin n)), T = L.image (fun y => s(v, y)) := ⟨_, rfl⟩
  have hTcard : T.card = a + 1 := by rw [hT, Finset.card_image_of_injective _ hinj, hLcard]
  have hTe : ∀ e ∈ T, e ∈ G.edgeSet ∧ ∀ w ∈ e, w ∈ B := by
    intro e he
    rw [hT] at he
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.1 he
    refine ⟨(hLmem l hl).1, fun w hw => ?_⟩
    rw [hB]
    rcases Sym2.mem_iff.1 hw with rfl | rfl
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem hl
  have hc := wkx6_hc G P D B (Fintype.card W) M hM0 hD (fun j => by
    by_cases hj : j = P v
    · refine ⟨part P j ∩ D, le_rfl, ∅, Finset.empty_subset _, ?_, ?_⟩
      · intro b hb hbj
        exact absurd (hj ▸ hBi b hb) hbj
      · have h1 := wkx6_inter_card (part P j) D
        have h2 := hs0 j
        rw [hBcard]
        simp only [Finset.card_empty]
        linarith
    · refine ⟨Finset.univ.filter (fun w => G.Adj v w ∧ P w = j) ∩ D, ?_, L, ?_, ?_, ?_⟩
      · intro x hx
        rw [Finset.mem_inter, Finset.mem_filter] at hx
        rw [Finset.mem_inter]
        exact ⟨(wkx_mem_part P j x).2 hx.1.2.2, hx.2⟩
      · intro x hx; exact (hLmem x hx).2.2
      · intro b hb hbj
        rw [hB, Finset.mem_insert] at hb
        rcases hb with rfl | hb
        · right
          intro c hc
          rw [Finset.mem_inter, Finset.mem_filter] at hc
          exact hc.1.2.1
        · left; exact hb
      · have h1 := wkx6_inter_card (Finset.univ.filter (fun w => G.Adj v w ∧ P w = j)) D
        have h2 : (wkx6_own G P v : ℝ) ≤
            (Finset.univ.filter (fun w => G.Adj v w ∧ P w = j)).card := by
          exact_mod_cast wkx6_maxcut G P hP v j
        rw [hBcard, hLcard]
        linarith)
  exact wkx6_edgecore F hr G hG P hext (P v) B hBi (by rw [hBcard]; exact hn) T hTe
    (by rw [hTcard]) D hc

open Classical in
theorem wkx6_stepE {W : Type*} [Fintype W] (F : SimpleGraph W) {n r a : ℕ} (hr : 0 < r)
    (G : SimpleGraph (Fin n)) (hG : F.Free G) (P : Fin n → Fin r)
    (hext : SimpleGraph.extremalNumber n F = (SimpleGraph.turanGraph n r).edgeFinset.card + a)
    (M s0 : ℝ) (hM0 : 0 ≤ M)
    (hD : ∀ y, (wkx6_miss G P y : ℝ) ≤ M)
    (hs0 : ∀ j, s0 ≤ (part P j).card)
    (hn : r * (2 * (a + 1)) ≤ n)
    (hbig : ((Fintype.card W + 2 * (a + 1) : ℕ) : ℝ) +
      ((Fintype.card W + 2 * (a + 1) : ℕ) : ℝ) * M < s0)
    (i : Fin r) : edgesIn G (part P i) ≤ a := by
  by_contra hlt
  push_neg at hlt
  unfold edgesIn at hlt
  obtain ⟨T, hTsub, hTcard⟩ := Finset.exists_subset_card_eq (show a + 1 ≤ _ from hlt)
  have hTmem : ∀ e ∈ T, e ∈ G.edgeSet ∧ ∀ w ∈ e, w ∈ part P i := by
    intro e he
    have := hTsub he
    simp only [Finset.mem_filter, SimpleGraph.mem_edgeFinset] at this
    exact this
  obtain ⟨B, hB⟩ : ∃ B : Finset (Fin n), B = Finset.univ.filter (fun v => ∃ e ∈ T, v ∈ e) :=
    ⟨_, rfl⟩
  have hBcard : B.card ≤ 2 * (a + 1) := by rw [hB, ← hTcard]; exact wkx6_vcard T
  have hBi : ∀ b ∈ B, P b = i := by
    intro b hb
    rw [hB, Finset.mem_filter] at hb
    obtain ⟨e, he, hbe⟩ := hb.2
    exact (wkx_mem_part P i b).1 ((hTmem e he).2 b hbe)
  have hTe : ∀ e ∈ T, e ∈ G.edgeSet ∧ ∀ w ∈ e, w ∈ B := by
    intro e he
    refine ⟨(hTmem e he).1, fun w hw => ?_⟩
    rw [hB, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, e, he, hw⟩
  have hM' : (0:ℝ) ≤ M := hM0
  have hc := wkx6_hc G P Finset.univ B (Fintype.card W) M hM0 (fun y _ => hD y) (fun j => by
    refine ⟨part P j ∩ Finset.univ, le_rfl, B, Finset.subset_univ _, fun b hb _ => Or.inl hb, ?_⟩
    rw [Finset.inter_univ]
    have h1 : ((Fintype.card W + B.card : ℕ) : ℝ) ≤ ((Fintype.card W + 2 * (a + 1) : ℕ) : ℝ) := by
      exact_mod_cast Nat.add_le_add_left hBcard _
    have h2 := mul_le_mul_of_nonneg_right h1 hM0
    have h3 := hs0 j
    linarith)
  exact wkx6_edgecore F hr G hG P hext i B hBi
    (le_trans (Nat.mul_le_mul_left r hBcard) hn) T hTe (by rw [hTcard]) Finset.univ hc

open Classical Matrix in
theorem wkx6_rowup {n r : ℕ} (G : SimpleGraph (Fin n)) (P : Fin n → Fin r) (x : Fin n → ℝ)
    (hev : (G.adjMatrix ℝ).mulVec x = specRad G • x) (hx1 : ∀ j, x j ≤ 1)
    (hx0 : ∀ j, 0 ≤ x j) (y : Fin n) :
    specRad G * x y ≤ (∑ q, (if P q ≠ P y then x q else 0)) + wkx6_own G P y := by
  have hrow : ∑ q, (if G.Adj y q then x q else 0) = specRad G * x y := by
    rw [← wk9_row G x y, hev]; simp
  have h1 : ∀ q, (if G.Adj y q then x q else 0) ≤ (if P q ≠ P y then x q else 0) +
      (if G.Adj y q ∧ P q = P y then (1:ℝ) else 0) := by
    intro q
    have h1 := hx1 q
    have h0 := hx0 q
    by_cases hq : P q = P y <;> by_cases ha : G.Adj y q <;> simp [hq, ha] <;> linarith
  have h2 := Finset.sum_le_sum (fun q (_ : q ∈ Finset.univ) => h1 q)
  rw [Finset.sum_add_distrib, Finset.sum_boole, hrow] at h2
  unfold wkx6_own
  exact h2

open Classical Matrix in
theorem wkx6_rowlow {n r : ℕ} (G : SimpleGraph (Fin n)) (P : Fin n → Fin r) (x : Fin n → ℝ)
    (hev : (G.adjMatrix ℝ).mulVec x = specRad G • x) (hx1 : ∀ j, x j ≤ 1)
    (hx0 : ∀ j, 0 ≤ x j) (y : Fin n) :
    (∑ q, (if P q ≠ P y then x q else 0)) - wkx6_miss G P y ≤ specRad G * x y := by
  have hrow : ∑ q, (if G.Adj y q then x q else 0) = specRad G * x y := by
    rw [← wk9_row G x y, hev]; simp
  have h1 : ∀ q, (if P q ≠ P y then x q else 0) -
      (if P q ≠ P y ∧ ¬ G.Adj y q then (1:ℝ) else 0) ≤ (if G.Adj y q then x q else 0) := by
    intro q
    have h1 := hx1 q
    have h0 := hx0 q
    by_cases hq : P q = P y <;> by_cases ha : G.Adj y q <;> simp [hq, ha] <;> linarith
  have h2 := Finset.sum_le_sum (fun q (_ : q ∈ Finset.univ) => h1 q)
  rw [Finset.sum_sub_distrib, Finset.sum_boole, hrow] at h2
  unfold wkx6_miss
  exact h2

open Classical in
theorem wkx6_ind {n r : ℕ} (P : Fin n → Fin r) (j : Fin r) :
    (∑ q, (if P q = j then (1:ℝ) else 0)) = (part P j).card := by
  rw [Finset.sum_boole]
  congr 2

open Classical Matrix in
theorem wkx6_Tlow {n r : ℕ} (G : SimpleGraph (Fin n)) (P : Fin n → Fin r) (x : Fin n → ℝ)
    (hev : (G.adjMatrix ℝ).mulVec x = specRad G • x) (hx1 : ∀ j, x j ≤ 1)
    (hx0 : ∀ j, 0 ≤ x j) (z : Fin n) (hz : x z = 1) (θn s0 : ℝ)
    (hown : ∀ y, (wkx6_own G P y : ℝ) ≤ θn) (hs0 : ∀ j, s0 ≤ (part P j).card)
    (hgap : (n:ℝ) - 5 / 3 * s0 < specRad G - θn) (hlam : 0 ≤ specRad G) (j : Fin r) :
    specRad G / 3 - θn ≤ ∑ q, (if P q ≠ j then x q else 0) := by
  have hex : ∃ y, P y = j ∧ 1 / 3 ≤ x y := by
    by_contra hne
    push_neg at hne
    have hjz : P z ≠ j := fun h => by have := hne z h; rw [hz] at this; norm_num at this
    have hup := wkx6_rowup G P x hev hx1 hx0 z
    rw [hz, mul_one] at hup
    have hpt : ∀ q, (if P q ≠ P z then x q else 0) ≤
        1 - (if P q = P z then (1:ℝ) else 0) - 2 / 3 * (if P q = j then (1:ℝ) else 0) := by
      intro q
      by_cases h1 : P q = P z
      · have h2 : ¬ P q = j := fun h => hjz (h1.symm.trans h)
        rw [if_neg (not_not.2 h1), if_pos h1, if_neg h2]; norm_num
      · rw [if_pos h1, if_neg h1]
        by_cases h2 : P q = j
        · rw [if_pos h2]; have := hne q h2; linarith
        · rw [if_neg h2]; linarith [hx1 q]
    have hs := Finset.sum_le_sum (fun q (_ : q ∈ Finset.univ) => hpt q)
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, wkx6_ind, wkx6_ind]
      at hs
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at hs
    have h1 := hs0 (P z)
    have h2 := hs0 j
    have h3 := hown z
    linarith
  obtain ⟨y, hyj, hy⟩ := hex
  have hup := wkx6_rowup G P x hev hx1 hx0 y
  rw [hyj] at hup
  have := hown y
  have h4 : specRad G / 3 ≤ specRad G * x y := by nlinarith
  linarith

/-- `G` with the edges at `u` replaced by all edges from `u` to `N`. -/
def wkx6G {n : ℕ} (G : SimpleGraph (Fin n)) (u : Fin n) (N : Finset (Fin n)) :
    SimpleGraph (Fin n) where
  Adj p q := p ≠ q ∧ ((p ≠ u ∧ q ≠ u ∧ G.Adj p q) ∨ (p = u ∧ q ∈ N) ∨ (q = u ∧ p ∈ N))
  symm := ⟨fun p q h => ⟨Ne.symm h.1, by
    rcases h.2 with ⟨h1, h2, h3⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨h2, h1, h3.symm⟩
    · exact Or.inr (Or.inr ⟨h1, h2⟩)
    · exact Or.inr (Or.inl ⟨h1, h2⟩)⟩⟩
  loopless := ⟨fun p h => h.1 rfl⟩

theorem wkx6G_adj {n : ℕ} (G : SimpleGraph (Fin n)) (u : Fin n) (N : Finset (Fin n))
    (p q : Fin n) :
    (wkx6G G u N).Adj p q ↔
      p ≠ q ∧ ((p ≠ u ∧ q ≠ u ∧ G.Adj p q) ∨ (p = u ∧ q ∈ N) ∨ (q = u ∧ p ∈ N)) :=
  Iff.rfl

theorem wkx6_free {W : Type*} [Fintype W] (F : SimpleGraph W) {n : ℕ}
    (G : SimpleGraph (Fin n)) (hG : F.Free G) (u : Fin n) (N : Finset (Fin n))
    (hc : ∀ X : Finset (Fin n), X.card ≤ Fintype.card W + 1 →
      ∃ c, c ∉ X ∧ ∀ w ∈ X, w ∈ N → G.Adj c w) :
    F.Free (wkx6G G u N) := by
  classical
  rintro ⟨f⟩
  apply hG
  obtain ⟨c, hcX, hcadj⟩ := hc (insert u (Finset.univ.image f.toHom)) (by
    have h1 := Finset.card_insert_le u (Finset.univ.image f.toHom)
    have h2 : (Finset.univ.image f.toHom).card ≤ Fintype.card W :=
      Finset.card_image_le.trans (by rw [Finset.card_univ])
    omega)
  have hcX' : ∀ q : W, f.toHom q ≠ c := fun q hq =>
    hcX (Finset.mem_insert_of_mem (hq ▸ Finset.mem_image_of_mem _ (Finset.mem_univ q)))
  have hmem : ∀ q : W, f.toHom q ∈ insert u (Finset.univ.image f.toHom) := fun q =>
    Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ q))
  refine ⟨⟨⟨fun p => if f.toHom p = u then c else f.toHom p, ?_⟩, ?_⟩⟩
  · intro p q hpq
    have hf : (wkx6G G u N).Adj (f.toHom p) (f.toHom q) := f.toHom.map_adj hpq
    rw [wkx6G_adj] at hf
    change G.Adj (if f.toHom p = u then c else f.toHom p)
      (if f.toHom q = u then c else f.toHom q)
    split_ifs with h1 h2 h2
    · exact absurd (f.injective (h1.trans h2.symm)) (F.ne_of_adj hpq)
    · have hq : f.toHom q ∈ N := by
        rcases hf.2 with ⟨h3, -, -⟩ | ⟨-, h4⟩ | ⟨h4, -⟩
        · exact absurd h1 h3
        · exact h4
        · exact absurd h4 h2
      exact hcadj _ (hmem q) hq
    · have hp : f.toHom p ∈ N := by
        rcases hf.2 with ⟨-, h3, -⟩ | ⟨h4, -⟩ | ⟨-, h4⟩
        · exact absurd h2 h3
        · exact absurd h4 h1
        · exact h4
      exact (hcadj _ (hmem p) hp).symm
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

open Classical Matrix in
theorem wkx6_key {n : ℕ} (G : SimpleGraph (Fin n)) (u : Fin n) (N : Finset (Fin n))
    (huN : u ∉ N) (hle : specRad (wkx6G G u N) ≤ specRad G) (x : Fin n → ℝ)
    (hev : (G.adjMatrix ℝ).mulVec x = specRad G • x) (hpos : ∀ j, 0 < x j) :
    (∑ q, (if q ∈ N then x q else 0)) ≤ ∑ q, (if G.Adj u q then x q else 0) := by
  have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) u.isLt
  have hR := wkx37_rayleigh (wkx6G G u N) hn x
  have hxx : 0 < x ⬝ᵥ x := by
    unfold dotProduct
    exact Finset.sum_pos (fun j _ => mul_pos (hpos j) (hpos j)) ⟨u, Finset.mem_univ _⟩
  have hA : x ⬝ᵥ (G.adjMatrix ℝ *ᵥ x) = specRad G * (x ⬝ᵥ x) := by
    rw [hev, dotProduct_smul, smul_eq_mul]
  rw [wk9_quad] at hR hA
  have hdiff := wkx38_quad_diff G (wkx6G G u N) u
    (fun p q hp hq => by
      rw [wkx6G_adj]
      constructor
      · rintro ⟨-, h | ⟨h, -⟩ | ⟨h, -⟩⟩
        · exact h.2.2
        · exact absurd h hp
        · exact absurd h hq
      · intro h; exact ⟨G.ne_of_adj h, Or.inl ⟨hp, hq, h⟩⟩) x
  have hiff : ∀ q, (wkx6G G u N).Adj u q ↔ q ∈ N := by
    intro q
    rw [wkx6G_adj]
    constructor
    · rintro ⟨-, ⟨h, -⟩ | ⟨-, h⟩ | ⟨-, h'⟩⟩
      · exact absurd rfl h
      · exact h
      · exact absurd h' huN
    · intro h; exact ⟨fun e => huN (e ▸ h), Or.inr (Or.inl ⟨rfl, h⟩)⟩
  have hrowN : (∑ q, (if (wkx6G G u N).Adj u q then x q else 0)) =
      ∑ q, (if q ∈ N then x q else 0) := by
    refine Finset.sum_congr rfl (fun q _ => ?_)
    by_cases h : q ∈ N
    · rw [if_pos ((hiff q).2 h), if_pos h]
    · rw [if_neg (fun h' => h ((hiff q).1 h')), if_neg h]
  have h1 : specRad (wkx6G G u N) * (x ⬝ᵥ x) ≤ specRad G * (x ⬝ᵥ x) :=
    mul_le_mul_of_nonneg_right hle hxx.le
  rw [hrowN] at hdiff
  by_contra hcon
  push Not at hcon
  have hp := mul_pos (mul_pos (two_pos : (0:ℝ) < 2) (hpos u)) (sub_pos.2 hcon)
  linarith

open Classical in
theorem wkx6_gain {n r : ℕ} (G : SimpleGraph (Fin n)) (P : Fin n → Fin r) (x : Fin n → ℝ)
    (hx1 : ∀ j, x j ≤ 1) (hx0 : ∀ j, 0 ≤ x j) (D : Finset (Fin n)) (v : Fin n)
    (hD6 : ∀ y ∈ D, P y ≠ P v → 1 / 6 ≤ x y)
    (hkey : (∑ q, (if q ∈ Finset.univ.filter (fun w => P w ≠ P v ∧ w ∈ D) then x q else 0)) ≤
      ∑ q, (if G.Adj v q then x q else 0)) :
    ((n:ℝ) - (part P (P v)).card) - G.degree v ≤
      7 * ((Finset.univ \ D).card : ℝ) + 6 * wkx6_own G P v := by
  have hpt : ∀ q, 1 / 6 * (if P q ≠ P v then (1:ℝ) else 0) -
      7 / 6 * (if q ∉ D then (1:ℝ) else 0) - 1 / 6 * (if G.Adj v q then (1:ℝ) else 0) -
      (if G.Adj v q ∧ P q = P v then (1:ℝ) else 0) ≤
      (if q ∈ Finset.univ.filter (fun w => P w ≠ P v ∧ w ∈ D) then x q else 0) -
        (if G.Adj v q then x q else 0) := by
    intro q
    have h1 := hx1 q
    have h0 := hx0 q
    by_cases hq1 : P q = P v <;> by_cases hq2 : q ∈ D <;> by_cases hq3 : G.Adj v q <;>
      simp [hq1, hq2, hq3] <;> first | linarith | linarith [hD6 q hq2 hq1]
  have hs := Finset.sum_le_sum (fun q (_ : q ∈ Finset.univ) => hpt q)
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_boole] at hs
  have e3 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
    (fun w => P w = P v)
  rw [Finset.card_univ, Fintype.card_fin] at e3
  have hp : (part P (P v)).card = (Finset.univ.filter (fun w => P w = P v)).card := by
    congr 1
  have q2 : (Finset.univ.filter (fun w => ¬ P w = P v)).card =
      (Finset.univ.filter (fun w => P w ≠ P v)).card := rfl
  have c2 : (Finset.univ.filter (fun q => q ∉ D)).card = (Finset.univ \ D).card := by
    congr 1; ext q; simp
  have hd : G.degree v = (Finset.univ.filter (fun q => G.Adj v q)).card := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    congr 1; ext w; simp
  have ho : wkx6_own G P v = (Finset.univ.filter (fun q => G.Adj v q ∧ P q = P v)).card := rfl
  have e3' : ((Finset.univ.filter (fun w => P w ≠ P v)).card : ℝ) + (part P (P v)).card = n := by
    have : (Finset.univ.filter (fun w => P w ≠ P v)).card + (part P (P v)).card = n := by
      omega
    exact_mod_cast this
  rw [c2, ← hd, ← ho] at hs
  linarith

open Classical in
theorem wkx6_stepD {W : Type*} [Fintype W] (F : SimpleGraph W) {n r : ℕ}
    (G : SimpleGraph (Fin n)) (hG : IsSpectralExtremal F G) (hconn : G.Connected)
    (P : Fin n → Fin r) (D : Finset (Fin n)) (M β θn s0 s1 : ℝ) (hM0 : 0 ≤ M)
    (hD : ∀ y ∈ D, (wkx6_miss G P y : ℝ) ≤ M)
    (hDc : ((Finset.univ \ D).card : ℝ) ≤ β)
    (hown : ∀ y, (wkx6_own G P y : ℝ) ≤ θn)
    (hs0 : ∀ j, s0 ≤ (part P j).card) (hs1 : ∀ j, ((part P j).card : ℝ) ≤ s1)
    (hlam0 : 0 < specRad G)
    (hgap : (n:ℝ) - 5 / 3 * s0 < specRad G - θn)
    (hsm : 6 * (θn + M) ≤ specRad G)
    (hbig : ((Fintype.card W + 1 : ℕ) : ℝ) + ((Fintype.card W + 1 : ℕ) : ℝ) * M < s0 - β)
    (v : Fin n) (dv : ℝ) (hdv : (G.degree v : ℝ) ≤ dv)
    (hfinal : 7 * β + 6 * θn < (n:ℝ) - s1 - dv) : False := by
  obtain ⟨x, hev, hpos, hx1, z, hz⟩ := wkx_perron_connected G hconn
  have hx0 : ∀ j, 0 ≤ x j := fun j => (hpos j).le
  obtain ⟨N', hN'⟩ : ∃ N' : Finset (Fin n),
      N' = Finset.univ.filter (fun w => P w ≠ P v ∧ w ∈ D) := ⟨_, rfl⟩
  have hvN : v ∉ N' := by
    rw [hN', Finset.mem_filter]; exact fun h => h.2.1 rfl
  have hfree : F.Free (wkx6G G v N') := wkx6_free F G hG.1 v N' (fun X hX => by
    obtain ⟨c, hcA, hcX, hcadj⟩ := wkx6_find G (part P (P v) ∩ D)
      (X.filter (fun w => w ∈ N')) X M
      (fun y hy => by
        rw [Finset.mem_filter, hN', Finset.mem_filter] at hy
        have hpm := wkx6_part_miss G P y (P v) hy.2.2.1 (part P (P v) ∩ D)
          Finset.inter_subset_left
        have hpm' : (((part P (P v) ∩ D) \ G.neighborFinset y).card : ℝ) ≤ wkx6_miss G P y := by
          exact_mod_cast hpm
        exact le_trans hpm' (hD y hy.2.2.2))
      (by
        have h1 := wkx6_inter_card (part P (P v)) D
        have h2 := hs0 (P v)
        have h3 : ((X.filter (fun w => w ∈ N')).card : ℝ) ≤ ((Fintype.card W + 1 : ℕ) : ℝ) := by
          exact_mod_cast (Finset.card_filter_le _ _).trans hX
        have h4 : (X.card : ℝ) ≤ ((Fintype.card W + 1 : ℕ) : ℝ) := by exact_mod_cast hX
        have h5 := mul_le_mul_of_nonneg_right h3 hM0
        linarith)
    exact ⟨c, hcX, fun w hw hwN => (hcadj w (Finset.mem_filter.2 ⟨hw, hwN⟩)).symm⟩)
  have hle := hG.2 _ hfree
  have hkey := wkx6_key G v N' hvN hle x hev hpos
  have hD6 : ∀ y ∈ D, P y ≠ P v → 1 / 6 ≤ x y := by
    intro y hy _
    have h1 := wkx6_rowlow G P x hev hx1 hx0 y
    have h2 := wkx6_Tlow G P x hev hx1 hx0 z hz θn s0 hown hs0 hgap hlam0.le (P y)
    have h3 := hD y hy
    have h4 : specRad G / 6 ≤ specRad G * x y := by linarith
    by_contra hc
    push Not at hc
    have := mul_lt_mul_of_pos_left hc hlam0
    linarith
  rw [hN'] at hkey
  have hg := wkx6_gain G P x hx1 hx0 D v hD6 hkey
  have h1 := hs1 (P v)
  have h2 := hown v
  linarith

open Classical Matrix in
theorem wkx6_lam {n r : ℕ} (G : SimpleGraph (Fin n)) (P : Fin n → Fin r) (hn : 0 < n)
    (s1 E : ℝ) (hs1 : ∀ j, ((part P j).card : ℝ) ≤ s1)
    (hE : ((completePartite P \ G).edgeFinset.card : ℝ) ≤ E) :
    (n:ℝ) - s1 - 2 * E / n ≤ specRad G := by
  have hR := wkx37_rayleigh G hn (fun _ => 1)
  have hq : (fun _ : Fin n => (1:ℝ)) ⬝ᵥ (G.adjMatrix ℝ *ᵥ (fun _ => 1)) =
      ∑ v, (G.degree v : ℝ) := by
    simp [dotProduct, SimpleGraph.adjMatrix_mulVec_apply]
  have h11 : (fun _ : Fin n => (1:ℝ)) ⬝ᵥ (fun _ => 1) = n := by
    simp [dotProduct]
  rw [hq, h11] at hR
  have hdeg : ∀ v, (n:ℝ) - s1 - wkx6_miss G P v ≤ G.degree v := by
    intro v
    have h0 := wkx6_deg_eq G P v
    have h' : ((G.degree v + wkx6_miss G P v + (part P (P v)).card : ℕ) : ℝ) =
        ((wkx6_own G P v + n : ℕ) : ℝ) := by rw [h0]
    push_cast at h'
    have := hs1 (P v)
    have : (0:ℝ) ≤ wkx6_own G P v := Nat.cast_nonneg _
    linarith
  have hsum : ∑ v, ((n:ℝ) - s1 - wkx6_miss G P v) ≤ ∑ v, (G.degree v : ℝ) :=
    Finset.sum_le_sum (fun v _ => hdeg v)
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul] at hsum
  have hm : ((∑ v, wkx6_miss G P v : ℕ) : ℝ) =
      2 * ((completePartite P \ G).edgeFinset.card : ℝ) := by
    rw [wkx6_sum_miss]; push_cast; ring
  push_cast at hm
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  have heq : ((n:ℝ) - s1 - 2 * E / n) * n = n * (n - s1) - 2 * E := by
    field_simp
  have hfin : ((n:ℝ) - s1 - 2 * E / n) * n ≤ specRad G * n := by
    rw [heq]; nlinarith
  exact le_of_mul_le_mul_right hfin hn'

open Classical in
theorem wkx6_coreD {n r : ℕ} (G : SimpleGraph (Fin n)) (P : Fin n → Fin r) (μ ε : ℝ)
    (hμ : 0 < μ) (hn0 : 0 < n)
    (hE : ((completePartite P \ G).edgeFinset.card : ℝ) ≤ 2 * ε * (n : ℝ) ^ 2) :
    ∃ D : Finset (Fin n), (∀ y ∈ D, (wkx6_miss G P y : ℝ) ≤ μ * n) ∧
      ((Finset.univ \ D).card : ℝ) ≤ 4 * ε * n / μ := by
  have hn' : (0:ℝ) < n := by exact_mod_cast hn0
  have hμn : 0 < μ * n := mul_pos hμ hn'
  obtain ⟨D, hDd⟩ : ∃ D : Finset (Fin n),
      D = Finset.univ.filter (fun y => (wkx6_miss G P y : ℝ) ≤ μ * n) := ⟨_, rfl⟩
  have hD : ∀ y ∈ D, (wkx6_miss G P y : ℝ) ≤ μ * n := by
    intro y hy; rw [hDd, Finset.mem_filter] at hy; exact hy.2
  have hDc : ((Finset.univ \ D).card : ℝ) ≤ 4 * ε * n / μ := by
    have hc := wkx6_count (wkx6_miss G P) (μ * n)
    have hsub : Finset.univ \ D ⊆
        Finset.univ.filter (fun v => μ * n ≤ (wkx6_miss G P v : ℝ)) := by
      intro y hy
      rw [Finset.mem_sdiff, hDd, Finset.mem_filter] at hy
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, le_of_lt (not_le.1 (fun h => hy.2 ⟨Finset.mem_univ _, h⟩))⟩
    have h1 : ((Finset.univ \ D).card : ℝ) ≤
        (Finset.univ.filter (fun v => μ * n ≤ (wkx6_miss G P v : ℝ))).card := by
      exact_mod_cast Finset.card_le_card hsub
    have hm : ((∑ v, wkx6_miss G P v : ℕ) : ℝ) =
        2 * ((completePartite P \ G).edgeFinset.card : ℝ) := by
      rw [wkx6_sum_miss]; push_cast; ring
    push_cast at hm
    have h2 := mul_le_mul_of_nonneg_right h1 hμn.le
    have h3 : ((Finset.univ \ D).card : ℝ) * (μ * n) ≤ 4 * ε * (n:ℝ) ^ 2 := by linarith
    rw [le_div_iff₀ hμ]
    by_contra hcon
    push Not at hcon
    have := mul_lt_mul_of_pos_right hcon hn'
    nlinarith
  exact ⟨D, hD, hDc⟩

open Classical in
theorem wkx6_core {W : Type*} [Fintype W] (F : SimpleGraph W) {n r a : ℕ} (hr : 2 ≤ r)
    (G : SimpleGraph (Fin n)) (hG : IsSpectralExtremal F G) (hconn : G.Connected)
    (P : Fin n → Fin r) (hP : IsMaxCut G P)
    (hext : SimpleGraph.extremalNumber n F = (SimpleGraph.turanGraph n r).edgeFinset.card + a)
    (η θ μ ε s : ℝ) (hθ : 0 < θ) (hμ : 0 < μ) (hε : 0 < ε) (hs0' : 0 ≤ s) (hη : 0 < η)
    (h33a : ((SimpleGraph.turanGraph n r).edgeFinset.card : ℝ) - ε * (n : ℝ) ^ 2 ≤
      G.edgeFinset.card)
    (h33b : ((∑ i, edgesIn G (part P i) : ℕ) : ℝ) ≤ ε * (n : ℝ) ^ 2)
    (h33c : ∀ i : Fin r, (1 / (r : ℝ) - 3 * s) * n < (part P i).card ∧
          ((part P i).card : ℝ) < (1 / (r : ℝ) + 3 * s) * n)
    (hn0 : 0 < n) (hn1 : r * (2 * (a + 2)) ≤ n)
    (N1 : ((Fintype.card W + (a + 2) : ℕ) : ℝ) + ((Fintype.card W + (a + 1) : ℕ) : ℝ) * (μ * n) <
      θ * n - 4 * ε * n / μ)
    (N2 : ((Fintype.card W + (a + 2) : ℕ) : ℝ) + ((Fintype.card W + 0 : ℕ) : ℝ) * (μ * n) <
      (1 / (r : ℝ) - 3 * s) * n - 4 * ε * n / μ)
    (N3 : 0 < (n:ℝ) - (1 / (r : ℝ) + 3 * s) * n - 4 * ε * n)
    (N4 : (n:ℝ) - 5 / 3 * ((1 / (r : ℝ) - 3 * s) * n) <
      ((n:ℝ) - (1 / (r : ℝ) + 3 * s) * n - 4 * ε * n) - θ * n)
    (N5 : 6 * (θ * n + μ * n) ≤ (n:ℝ) - (1 / (r : ℝ) + 3 * s) * n - 4 * ε * n)
    (N6 : ((Fintype.card W + 1 : ℕ) : ℝ) + ((Fintype.card W + 1 : ℕ) : ℝ) * (μ * n) <
      (1 / (r : ℝ) - 3 * s) * n - 4 * ε * n / μ)
    (N7 : 7 * (4 * ε * n / μ) + 6 * (θ * n) <
      (n:ℝ) - (1 / (r : ℝ) + 3 * s) * n - (1 - 1 / (r:ℝ) - η) * n)
    (N8 : ((Fintype.card W + 2 * (a + 1) : ℕ) : ℝ) +
      ((Fintype.card W + 2 * (a + 1) : ℕ) : ℝ) * (θ * n + η * n + 3 * s * n) <
      (1 / (r : ℝ) - 3 * s) * n) :
    (∀ v : Fin n, (1 - 1 / (r : ℝ) - η) * n < (G.degree v : ℝ)) ∧
      ∀ i : Fin r, edgesIn G (part P i) ≤ a := by
  have hr0 : 0 < r := by omega
  have hn' : (0:ℝ) < n := by exact_mod_cast hn0
  have hμn : 0 < μ * n := mul_pos hμ hn'
  have hE := wkx6_KPG G P ε h33a h33b
  obtain ⟨D, hD, hDc⟩ := wkx6_coreD G P μ ε hμ hn0 hE
  have hrn : r * (a + 2) ≤ n := le_trans (Nat.mul_le_mul_left r (by omega)) hn1
  have hownlt : ∀ v, (wkx6_own G P v : ℝ) < θ * n := by
    intro v
    by_contra hc
    push Not at hc
    exact wkx6_stepC F hr0 G hG.1 P hP hext D (μ * n) (4 * ε * n / μ)
      ((1 / (r : ℝ) - 3 * s) * n) hμn.le hD hDc (fun j => (h33c j).1.le) hrn v (θ * n) hc N1 N2
  have hlam := wkx6_lam G P hn0 ((1 / (r : ℝ) + 3 * s) * n) (2 * ε * (n:ℝ) ^ 2)
    (fun j => (h33c j).2.le) hE
  have h2E : 2 * (2 * ε * (n:ℝ) ^ 2) / n = 4 * ε * n := by
    rw [div_eq_iff hn'.ne']; ring
  rw [h2E] at hlam
  have hdeg : ∀ v : Fin n, (1 - 1 / (r : ℝ) - η) * n < (G.degree v : ℝ) := by
    intro v
    by_contra hc
    push Not at hc
    exact wkx6_stepD F G hG hconn P D (μ * n) (4 * ε * n / μ) (θ * n)
      ((1 / (r : ℝ) - 3 * s) * n) ((1 / (r : ℝ) + 3 * s) * n) hμn.le hD hDc
      (fun y => (hownlt y).le) (fun j => (h33c j).1.le) (fun j => (h33c j).2.le)
      (by linarith) (by linarith) (by linarith) N6 v _ hc N7
  refine ⟨hdeg, fun i => wkx6_stepE F hr0 G hG.1 P hext (θ * n + η * n + 3 * s * n)
    ((1 / (r : ℝ) - 3 * s) * n)
    (by nlinarith [mul_pos hθ hn', mul_pos hη hn', mul_nonneg hs0' hn'.le]) (fun y => ?_)
    (fun j => (h33c j).1.le) (le_trans (Nat.mul_le_mul_left r (by omega)) hn1) N8 i⟩
  have h1 := wkx6_deg_eq G P y
  have h1' : ((G.degree y + wkx6_miss G P y + (part P (P y)).card : ℕ) : ℝ) =
      ((wkx6_own G P y + n : ℕ) : ℝ) := by rw [h1]
  push_cast at h1'
  have h2 := hdeg y
  have h3 := hownlt y
  have h4 := (h33c (P y)).1
  nlinarith

theorem wkx6_num (k a r : ℕ) (hr : 2 ≤ r) (η : ℝ) (hη : 0 < η)
    (hη1 : η ≤ 1 / (8 * (r:ℝ) * ((k:ℝ) + 2 * a + 3))) :
    ∃ θ μ ε s : ℝ, 0 < θ ∧ 0 < μ ∧ 0 < ε ∧ 0 ≤ s ∧ Real.sqrt ε = s ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      0 < n ∧ r * (2 * (a + 2)) ≤ n ∧
      ((k + (a + 2) : ℕ) : ℝ) + ((k + (a + 1) : ℕ) : ℝ) * (μ * n) < θ * n - 4 * ε * n / μ ∧
      ((k + (a + 2) : ℕ) : ℝ) + ((k + 0 : ℕ) : ℝ) * (μ * n) <
        (1 / (r : ℝ) - 3 * s) * n - 4 * ε * n / μ ∧
      0 < (n:ℝ) - (1 / (r : ℝ) + 3 * s) * n - 4 * ε * n ∧
      (n:ℝ) - 5 / 3 * ((1 / (r : ℝ) - 3 * s) * n) <
        ((n:ℝ) - (1 / (r : ℝ) + 3 * s) * n - 4 * ε * n) - θ * n ∧
      6 * (θ * n + μ * n) ≤ (n:ℝ) - (1 / (r : ℝ) + 3 * s) * n - 4 * ε * n ∧
      ((k + 1 : ℕ) : ℝ) + ((k + 1 : ℕ) : ℝ) * (μ * n) <
        (1 / (r : ℝ) - 3 * s) * n - 4 * ε * n / μ ∧
      7 * (4 * ε * n / μ) + 6 * (θ * n) <
        (n:ℝ) - (1 / (r : ℝ) + 3 * s) * n - (1 - 1 / (r:ℝ) - η) * n ∧
      ((k + 2 * (a + 1) : ℕ) : ℝ) + ((k + 2 * (a + 1) : ℕ) : ℝ) * (θ * n + η * n + 3 * s * n) <
        (1 / (r : ℝ) - 3 * s) * n := by
  have hR : (2:ℝ) ≤ r := by exact_mod_cast hr
  have hR0 : (0:ℝ) < r := by linarith
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ℝ, ρ = 1 / (r:ℝ) := ⟨_, rfl⟩
  have hρ0 : 0 < ρ := by rw [hρ]; exact one_div_pos.2 hR0
  have hρr : ρ * r = 1 := by rw [hρ]; field_simp
  have hρ2 : ρ ≤ 1 / 2 := by rw [hρ]; exact one_div_le_one_div_of_le (by norm_num) hR
  have hk0 : (0:ℝ) ≤ k := Nat.cast_nonneg _
  have ha0 : (0:ℝ) ≤ a := Nat.cast_nonneg _
  obtain ⟨K2, hK2⟩ : ∃ K2 : ℝ, K2 = (k:ℝ) + 2 * a + 3 := ⟨_, rfl⟩
  have hK2p : 3 ≤ K2 := by rw [hK2]; linarith
  have hηρ : η * (8 * K2) ≤ ρ := by
    have e : 1 / (8 * (r:ℝ) * ((k:ℝ) + 2 * a + 3)) = ρ / (8 * K2) := by
      rw [hρ, hK2]; field_simp
    rw [e, le_div_iff₀ (by positivity)] at hη1
    exact hη1
  obtain ⟨θ, hθd⟩ : ∃ θ : ℝ, θ = η / 14 := ⟨_, rfl⟩
  obtain ⟨K1, hK1⟩ : ∃ K1 : ℝ, K1 = (k:ℝ) + a + 3 := ⟨_, rfl⟩
  have hK1p : 3 ≤ K1 := by rw [hK1]; linarith
  obtain ⟨μ, hμd⟩ : ∃ μ : ℝ, μ = θ / (4 * K1) := ⟨_, rfl⟩
  have hθ : 0 < θ := by rw [hθd]; positivity
  have hμ : 0 < μ := by rw [hμd]; exact div_pos hθ (by linarith)
  have hμK : μ * (4 * K1) = θ := by rw [hμd]; field_simp
  have hθρ : θ * 336 ≤ ρ := by
    have : η * 24 ≤ η * (8 * K2) := mul_le_mul_of_nonneg_left (by linarith) hη.le
    rw [hθd]; linarith
  have hμθ : μ * 12 ≤ θ := by
    have : μ * 12 ≤ μ * (4 * K1) := mul_le_mul_of_nonneg_left (by linarith) hμ.le
    linarith
  have hμ1 : μ ≤ 1 := by linarith
  obtain ⟨s, hsd⟩ : ∃ s : ℝ, s = μ ^ 2 / 100 := ⟨_, rfl⟩
  have hs : 0 < s := by rw [hsd]; positivity
  have hsμ : s * 100 ≤ μ := by
    have : μ ^ 2 ≤ μ := by
      rw [sq]; exact mul_le_of_le_one_left hμ.le hμ1
    rw [hsd]; linarith
  obtain ⟨ε, hεd⟩ : ∃ ε : ℝ, ε = s ^ 2 := ⟨_, rfl⟩
  have hε : 0 < ε := by rw [hεd]; positivity
  have hsq : Real.sqrt ε = s := by rw [hεd]; exact Real.sqrt_sq hs.le
  have hε4 : 4 * ε ≤ s := by
    have : s * (4 * s) ≤ s * 1 := mul_le_mul_of_nonneg_left (by linarith) hs.le
    rw [hεd]; nlinarith
  have h4εμ : 4 * ε / μ ≤ s := by
    rw [div_le_iff₀ hμ, hεd]
    have : s * (4 * s) ≤ s * μ := mul_le_mul_of_nonneg_left (by linarith) hs.le
    nlinarith
  have hA1 : ((k + (a + 1) : ℕ) : ℝ) * μ ≤ θ / 4 := by
    push_cast
    have : ((k:ℝ) + (a + 1)) * μ ≤ K1 * μ :=
      mul_le_mul_of_nonneg_right (by rw [hK1]; linarith) hμ.le
    linarith
  have hA2 : ((k + 0 : ℕ) : ℝ) * μ ≤ θ / 4 := by
    push_cast
    have : (k:ℝ) * μ ≤ K1 * μ := mul_le_mul_of_nonneg_right (by rw [hK1]; linarith) hμ.le
    linarith
  have hA3 : ((k + 1 : ℕ) : ℝ) * μ ≤ θ / 4 := by
    push_cast
    have : ((k:ℝ) + 1) * μ ≤ K1 * μ := mul_le_mul_of_nonneg_right (by rw [hK1]; linarith) hμ.le
    linarith
  have hA4 : ((k + 2 * (a + 1) : ℕ) : ℝ) * (θ + η + 3 * s) ≤ ρ / 4 := by
    push_cast
    have h1 : θ + η + 3 * s ≤ 2 * η := by rw [hθd] at hμθ ⊢; linarith
    have h2 : ((k:ℝ) + 2 * (a + 1)) ≤ K2 := by rw [hK2]; linarith
    have h3 : 0 ≤ θ + η + 3 * s := by positivity
    calc ((k:ℝ) + 2 * (a + 1)) * (θ + η + 3 * s) ≤ K2 * (θ + η + 3 * s) :=
          mul_le_mul_of_nonneg_right h2 h3
      _ ≤ K2 * (2 * η) := mul_le_mul_of_nonneg_left h1 (by linarith)
      _ = η * (8 * K2) / 4 := by ring
      _ ≤ ρ / 4 := by linarith
  obtain ⟨N0, hN0⟩ := exists_nat_ge (2 * K2 / θ + 2 * K2 * r)
  refine ⟨θ, μ, ε, s, hθ, hμ, hε, hs.le, hsq, max N0 (r * (2 * (a + 2))) + 1,
    fun n hn => ?_⟩
  have hn0 : 0 < n := by omega
  have hn1 : r * (2 * (a + 2)) ≤ n := by omega
  have hnR : (N0 : ℝ) ≤ n := by exact_mod_cast (by omega : N0 ≤ n)
  have hn' : (0:ℝ) < n := by exact_mod_cast hn0
  have hθn : 2 * K2 ≤ θ * n := by
    have h1 : 2 * K2 / θ ≤ n := by
      have : (0:ℝ) ≤ 2 * K2 * r := by positivity
      linarith
    rw [div_le_iff₀ hθ] at h1
    linarith
  have hρn : 2 * K2 ≤ ρ * n := by
    have h1 : 2 * K2 * r ≤ n := by
      have : (0:ℝ) ≤ 2 * K2 / θ := by positivity
      linarith
    have h2 := mul_le_mul_of_nonneg_left h1 hρ0.le
    have h3 : ρ * (2 * K2 * r) = 2 * K2 := by
      rw [show ρ * (2 * K2 * r) = 2 * K2 * (ρ * r) by ring, hρr, mul_one]
    linarith
  have h4n : 4 * ε * n / μ ≤ s * n := by
    have : 4 * ε * n / μ = 4 * ε / μ * n := by ring
    rw [this]; exact mul_le_mul_of_nonneg_right h4εμ hn'.le
  have hB1 := mul_le_mul_of_nonneg_right hA1 hn'.le
  have hB2 := mul_le_mul_of_nonneg_right hA2 hn'.le
  have hB3 := mul_le_mul_of_nonneg_right hA3 hn'.le
  have hB4 := mul_le_mul_of_nonneg_right hA4 hn'.le
  have hc1 : ((k + (a + 2) : ℕ) : ℝ) ≤ K2 := by push_cast; rw [hK2]; linarith
  have hc2 : ((k + 1 : ℕ) : ℝ) ≤ K2 := by push_cast; rw [hK2]; linarith
  have hc3 : ((k + 2 * (a + 1) : ℕ) : ℝ) ≤ K2 := by push_cast; rw [hK2]; linarith
  have hsn : 0 ≤ s * n := by positivity
  have hεn : 4 * ε * n ≤ s * n := mul_le_mul_of_nonneg_right hε4 hn'.le
  have hsθ : s * 100 ≤ θ := by linarith
  have hsθn : s * n ≤ θ * n / 100 := by
    have := mul_le_mul_of_nonneg_right hsθ hn'.le; linarith
  have hθρn : θ * n ≤ ρ * n / 336 := by
    have := mul_le_mul_of_nonneg_right hθρ hn'.le; linarith
  have hρhn : ρ * n ≤ n / 2 := by
    have := mul_le_mul_of_nonneg_right hρ2 hn'.le; linarith
  have hμθn : μ * n ≤ θ * n / 12 := by
    have := mul_le_mul_of_nonneg_right hμθ hn'.le; linarith
  have hθηn : θ * n = η * n / 14 := by rw [hθd]; ring
  have hηn : 0 < η * n := mul_pos hη hn'
  have hK2n : (0:ℝ) < K2 := by linarith
  rw [← hρ]
  refine ⟨hn0, hn1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · linarith
  · linarith
  · linarith
  · linarith
  · linarith
  · linarith
  · linarith
  · linarith

open Classical in
theorem wkx6_main {W : Type*} [Fintype W] (F : SimpleGraph W) (r a : ℕ) (hr : 2 ≤ r)
    (hF : TuranPlusEdges F r a)
    (h33 : ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ G : SimpleGraph (Fin n),
      IsSpectralExtremal F G →
      ((SimpleGraph.turanGraph n r).edgeFinset.card - ε * (n : ℝ) ^ 2 ≤ G.edgeFinset.card) ∧
      ∀ P : Fin n → Fin r, IsMaxCut G P →
        ((∑ i, edgesIn G (part P i) : ℕ) : ℝ) ≤ ε * (n : ℝ) ^ 2 ∧
        ∀ i : Fin r,
          (1 / (r : ℝ) - 3 * Real.sqrt ε) * n < (part P i).card ∧
          ((part P i).card : ℝ) < (1 / (r : ℝ) + 3 * Real.sqrt ε) * n)
    (h31 : ∃ N : ℕ, ∀ n ≥ N, ∀ G : SimpleGraph (Fin n), IsSpectralExtremal F G → G.Connected)
    (η : ℝ) (hη : 0 < η) (hη1 : η ≤ 1 / (8 * (r:ℝ) * ((Fintype.card W : ℝ) + 2 * a + 3))) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ G : SimpleGraph (Fin n), IsSpectralExtremal F G →
      ∀ P : Fin n → Fin r, IsMaxCut G P →
        (∀ v : Fin n, (1 - 1 / (r : ℝ) - η) * n < (G.degree v : ℝ)) ∧
        ∀ i : Fin r, edgesIn G (part P i) ≤ a := by
  obtain ⟨θ, μ, ε, s, hθ, hμ, hε, hs, hsq, N, hN⟩ := wkx6_num (Fintype.card W) a r hr η hη hη1
  obtain ⟨n₃, hn₃⟩ := h33 ε hε
  obtain ⟨N1, hN1⟩ := h31
  obtain ⟨NT, hNT⟩ := hF
  refine ⟨max (max N n₃) (max N1 NT), fun n hn G hG P hP => ?_⟩
  have hnN : N ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hn3 : n₃ ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have hn1' : N1 ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
  have hnT : NT ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn
  obtain ⟨hpos, hn1, c1, c2, c3, c4, c5, c6, c7, c8⟩ := hN n hnN
  obtain ⟨ha, hb⟩ := hn₃ n hn3 G hG
  obtain ⟨hb1, hb2⟩ := hb P hP
  rw [hsq] at hb2
  exact wkx6_core F hr G hG (hN1 n hn1' G hG) P hP (hNT n hnT).1 η θ μ ε s hθ hμ hε hs hη
    ha hb1 hb2 hpos hn1 c1 c2 c3 c4 c5 c6 c7 c8

open Classical in
theorem wkx6_final {W : Type*} [Fintype W] (F : SimpleGraph W) (r a : ℕ) (hr : 2 ≤ r)
    (hF : TuranPlusEdges F r a)
    (h33 : ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ G : SimpleGraph (Fin n),
      IsSpectralExtremal F G →
      ((SimpleGraph.turanGraph n r).edgeFinset.card - ε * (n : ℝ) ^ 2 ≤ G.edgeFinset.card) ∧
      ∀ P : Fin n → Fin r, IsMaxCut G P →
        ((∑ i, edgesIn G (part P i) : ℕ) : ℝ) ≤ ε * (n : ℝ) ^ 2 ∧
        ∀ i : Fin r,
          (1 / (r : ℝ) - 3 * Real.sqrt ε) * n < (part P i).card ∧
          ((part P i).card : ℝ) < (1 / (r : ℝ) + 3 * Real.sqrt ε) * n)
    (h31 : ∃ N : ℕ, ∀ n ≥ N, ∀ G : SimpleGraph (Fin n), IsSpectralExtremal F G → G.Connected) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ G : SimpleGraph (Fin n), IsSpectralExtremal F G →
        ∀ P : Fin n → Fin r, IsMaxCut G P →
          (∀ v : Fin n,
            (1 - 1 / (r : ℝ) - 3 * r * ε ^ ((1 : ℝ) / 3)) * n < (G.degree v : ℝ)) ∧
          ∀ i : Fin r, edgesIn G (part P i) ≤ a := by
  have hR0 : (0:ℝ) < r := by exact_mod_cast (by omega : 0 < r)
  obtain ⟨η0, hη0⟩ : ∃ η0 : ℝ,
      η0 = 1 / (8 * (r:ℝ) * ((Fintype.card W : ℝ) + 2 * a + 3)) := ⟨_, rfl⟩
  have hη0pos : 0 < η0 := by
    rw [hη0]
    have : (0:ℝ) < 8 * (r:ℝ) * ((Fintype.card W : ℝ) + 2 * a + 3) := by
      have h1 : (0:ℝ) < (Fintype.card W : ℝ) + 2 * a + 3 := by positivity
      have h2 : (0:ℝ) < 8 * (r:ℝ) := by linarith
      exact mul_pos h2 h1
    exact one_div_pos.2 this
  have h3r : (0:ℝ) < 3 * r := by linarith
  refine ⟨(η0 / (3 * r)) ^ 3, by positivity, fun ε hε hεlt => ?_⟩
  have hroot : ε ^ ((1:ℝ) / 3) ≤ η0 / (3 * r) := by
    calc ε ^ ((1:ℝ) / 3) ≤ ((η0 / (3 * r)) ^ 3) ^ ((1:ℝ) / 3) :=
          Real.rpow_le_rpow hε.le hεlt.le (by norm_num)
      _ = η0 / (3 * r) := by
          rw [show ((1:ℝ) / 3) = ((3:ℕ):ℝ)⁻¹ by norm_num]
          exact Real.pow_rpow_inv_natCast (by positivity) (by norm_num)
  have hηpos : 0 < 3 * (r:ℝ) * ε ^ ((1:ℝ) / 3) := by
    have := Real.rpow_pos_of_pos hε ((1:ℝ) / 3)
    exact mul_pos h3r this
  have hηle : 3 * (r:ℝ) * ε ^ ((1:ℝ) / 3) ≤ η0 := by
    calc 3 * (r:ℝ) * ε ^ ((1:ℝ) / 3) ≤ 3 * r * (η0 / (3 * r)) :=
          mul_le_mul_of_nonneg_left hroot h3r.le
      _ = η0 := by field_simp
  rw [hη0] at hηle
  exact wkx6_main F r a hr hF h33 h31 _ hηpos hηle

end WKX6

open WangKangXue.SpectralTuran Classical in
-- Lemma 3.6 (Wang-Kang-Xue) by reduction to Lemma 3.3 (stability) and Lemma 3.1 (connectivity).
theorem solution {W : Type*} [Fintype W] (F : SimpleGraph W) (r a : ℕ) (hr : 2 ≤ r)
    (hF : TuranPlusEdges F r a) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ G : SimpleGraph (Fin n), IsSpectralExtremal F G →
        ∀ P : Fin n → Fin r, IsMaxCut G P →
          (∀ v : Fin n,
            (1 - 1 / (r : ℝ) - 3 * r * ε ^ ((1 : ℝ) / 3)) * n < (G.degree v : ℝ)) ∧
          ∀ i : Fin r, edgesIn G (part P i) ≤ a := by
  exact wkx6_final F r a hr hF (lemma_3_3 F r a hr hF) (lemma_3_1 F r a hr hF)
