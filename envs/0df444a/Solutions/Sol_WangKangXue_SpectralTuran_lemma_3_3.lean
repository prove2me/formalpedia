-- Prove2me | solution 1 for WangKangXue.SpectralTuran.lemma_3_3
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-17T12:37:21.208828+00:00
-- url     : https://prove2.me/submissions/71f3933c-acbd-4e20-8b38-7c9573ec3f2a

import Mathlib
import Definitions.Def_WangKangXue_SpectralTuran_specRad
import Definitions.Def_WangKangXue_SpectralTuran_IsSpectralExtremal
import Definitions.Def_WangKangXue_SpectralTuran_TuranPlusEdges
import Definitions.Def_WangKangXue_SpectralTuran_edgesIn
import Definitions.Def_WangKangXue_SpectralTuran_IsMaxCut
import Theorems.Thm_WangKangXue_SpectralTuran_corollary_2_6

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


section WKX33

open WangKangXue.SpectralTuran

open Classical in
theorem wkx_exists_extremal {W : Type*} (F : SimpleGraph W) {n : ℕ} (G : SimpleGraph (Fin n))
    (hG : F.Free G) :
    ∃ H : SimpleGraph (Fin n), F.Free H ∧ H.edgeFinset.card = SimpleGraph.extremalNumber n F := by
  obtain ⟨H, inst, hH⟩ := (SimpleGraph.exists_isExtremal_iff_exists F.Free).2 ⟨G, hG⟩
  rw [SimpleGraph.isExtremal_free_iff, Fintype.card_fin] at hH
  exact ⟨H, hH.1, by convert hH.2⟩


open Classical Matrix in
theorem wkx37_rayleigh {n : ℕ} (H : SimpleGraph (Fin n)) (hn : 0 < n) (y : Fin n → ℝ) :
    y ⬝ᵥ (H.adjMatrix ℝ *ᵥ y) ≤ specRad H * (y ⬝ᵥ y) := by
  have hn0 : 0 < Fintype.card (Fin n) := by simpa using hn
  have hs : specRad H = (H.isHermitian_adjMatrix ℝ).eigenvalues₀ ⟨0, hn0⟩ := by
    unfold specRad; rw [dif_pos hn0]
  rw [hs]
  exact wk9_le (H.isHermitian_adjMatrix ℝ) hn0 y


theorem wkx_mem_part {n r : ℕ} (P : Fin n → Fin r) (i : Fin r) (v : Fin n) :
    v ∈ part P i ↔ P v = i := by
  unfold part; simp

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

open Classical in
theorem wkx33_nonadj_card {n r : ℕ} (hr : 0 < r) (T : SimpleGraph (Fin n))
    (hTadj : ∀ u w, T.Adj u w ↔ (u : ℕ) % r ≠ (w : ℕ) % r) (i : Fin n) :
    (Finset.univ.filter (fun y => ¬ T.Adj i y)).card ≤ n / r + 1 := by
  have h := Finset.card_le_card_of_injOn (s := Finset.univ.filter (fun y => ¬ T.Adj i y))
    (t := Finset.range (n / r + 1)) (fun y : Fin n => (y : ℕ) / r) ?_ ?_
  · simpa using h
  · intro y _
    have h1 : (y : ℕ) / r ≤ n / r := Nat.div_le_div_right y.isLt.le
    simp only [Finset.coe_range, Set.mem_Iio]
    omega
  · intro y hy z hz hyz
    have hy' : ¬ T.Adj i y := by simpa using hy
    have hz' : ¬ T.Adj i z := by simpa using hz
    rw [hTadj, not_not] at hy' hz'
    simp only at hyz
    apply Fin.ext
    calc (y : ℕ) = r * ((y : ℕ) / r) + (y : ℕ) % r := (Nat.div_add_mod _ _).symm
      _ = r * ((z : ℕ) / r) + (z : ℕ) % r := by rw [hyz, ← hy', ← hz']
      _ = z := Nat.div_add_mod _ _

open Classical in
theorem wkx33_deg_low {n r : ℕ} (hr : 0 < r) (T : SimpleGraph (Fin n))
    (hTadj : ∀ u w, T.Adj u w ↔ (u : ℕ) % r ≠ (w : ℕ) % r) (i : Fin n) :
    (n : ℝ) - n / r - 1 ≤ (Finset.univ.filter (fun y => T.Adj i y)).card := by
  have h1 := wkx33_nonadj_card hr T hTadj i
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin n))) (fun y => T.Adj i y)
  rw [Finset.card_univ, Fintype.card_fin] at hsplit
  have hR : ((Finset.univ.filter (fun y => T.Adj i y)).card : ℝ) +
      ((Finset.univ.filter (fun y => ¬ T.Adj i y)).card : ℝ) = n := by exact_mod_cast hsplit
  have h1R : ((Finset.univ.filter (fun y => ¬ T.Adj i y)).card : ℝ) ≤ ((n / r : ℕ) : ℝ) + 1 := by
    exact_mod_cast h1
  have hdiv : ((n / r : ℕ) : ℝ) ≤ (n : ℝ) / r := Nat.cast_div_le
  linarith

open Classical Matrix in
theorem wkx33_turan_lam {n r : ℕ} (hr : 0 < r) (hn : 0 < n) (T : SimpleGraph (Fin n))
    (hTadj : ∀ u w, T.Adj u w ↔ (u : ℕ) % r ≠ (w : ℕ) % r) :
    (1 - 1 / (r : ℝ)) * n - 1 ≤ specRad T := by
  have hR := wkx37_rayleigh T hn (fun _ : Fin n => (1 : ℝ))
  rw [wk9_quad] at hR
  beta_reduce at hR
  have h11 : ((fun _ : Fin n => (1 : ℝ)) ⬝ᵥ (fun _ : Fin n => (1 : ℝ)) : ℝ) = n := by
    simp [dotProduct]
  rw [h11] at hR
  have hrow : ∀ i : Fin n, (n : ℝ) - n / r - 1 ≤
      ∑ j, (if T.Adj i j then (1 : ℝ) * 1 else 0) := by
    intro i
    have hs : (∑ j, (if T.Adj i j then (1 : ℝ) * 1 else 0)) =
        ((Finset.univ.filter (fun y => T.Adj i y)).card : ℝ) := by
      rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul,
        mul_one, mul_one]
    rw [hs]
    exact wkx33_deg_low hr T hTadj i
  have hsum : (n : ℝ) * ((n : ℝ) - n / r - 1) ≤
      ∑ i, ∑ j, (if T.Adj i j then (1 : ℝ) * 1 else 0) := by
    have := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hrow i)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
    exact this
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hfin : (n : ℝ) * ((n : ℝ) - n / r - 1) ≤ specRad T * n :=
    le_trans hsum (by convert hR using 1)
  have e1 : (1 - 1 / (r : ℝ)) * n - 1 = (n : ℝ) - n / r - 1 := by ring
  rw [e1]
  by_contra hlt
  have := mul_lt_mul_of_pos_right (not_le.1 hlt) hnR
  linarith

open Classical in
theorem wkx33_turan_edges {n r : ℕ} (hr : 0 < r) (T : SimpleGraph (Fin n))
    (hTadj : ∀ u w, T.Adj u w ↔ (u : ℕ) % r ≠ (w : ℕ) % r) :
    (n : ℝ) * ((n : ℝ) - n / r - 1) ≤ 2 * (T.edgeFinset.card : ℝ) := by
  have h := T.sum_degrees_eq_twice_card_edges
  have hdeg : ∀ i, (n : ℝ) - n / r - 1 ≤ (T.degree i : ℝ) := by
    intro i
    rw [← SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.neighborFinset_eq_filter]
    exact wkx33_deg_low hr T hTadj i
  have hsum : (n : ℝ) * ((n : ℝ) - n / r - 1) ≤ ∑ i, (T.degree i : ℝ) := by
    have := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hdeg i)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
    exact this
  have h2 : (∑ i, (T.degree i : ℝ)) = 2 * (T.edgeFinset.card : ℝ) := by exact_mod_cast h
  linarith

open Classical in
theorem wkx33_mem_inf {V : Type*} [Fintype V] (G K : SimpleGraph V) (e : Sym2 V) :
    e ∈ (G ⊓ K).edgeFinset ↔ e ∈ G.edgeSet ∧ e ∈ K.edgeSet := by
  rw [SimpleGraph.mem_edgeFinset, SimpleGraph.edgeSet_inf]; rfl

theorem wkx33_card_inst {V : Type*} [Fintype V] (G : SimpleGraph V) (i1 i2 : Fintype G.edgeSet) :
    (@SimpleGraph.edgeFinset V G i1).card = (@SimpleGraph.edgeFinset V G i2).card := by
  rw [Subsingleton.elim i1 i2]

theorem wkx33_cardsplit {α : Type*} (s a b : Finset α) (p : α → Prop) [DecidablePred p]
    (ha : ∀ x, x ∈ a ↔ x ∈ s ∧ p x) (hb : ∀ x, x ∈ b ↔ x ∈ s ∧ ¬ p x) :
    a.card + b.card = s.card := by
  have e1 : a = s.filter p := by ext x; rw [ha, Finset.mem_filter]
  have e2 : b = s.filter (fun x => ¬ p x) := by ext x; rw [hb, Finset.mem_filter]
  rw [e1, e2, Finset.card_filter_add_card_filter_not]

open Classical in
theorem wkx33_in_cross {n r : ℕ} (G : SimpleGraph (Fin n)) (P : Fin n → Fin r) :
    ∑ i, edgesIn G (part P i) + crossEdges G P ≤ G.edgeFinset.card := by
  have h1 := wkx39_in_le G P
  have h2 : crossEdges G P + (G \ completePartite P).edgeFinset.card = G.edgeFinset.card := by
    unfold crossEdges
    apply wkx33_cardsplit _ _ _ (fun e => e ∈ (completePartite P).edgeSet)
    · intro e
      rw [wkx33_mem_inf, SimpleGraph.mem_edgeFinset]
    · intro e
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.edgeSet_sdiff, Set.mem_sdiff,
        SimpleGraph.mem_edgeFinset]
  omega

open Classical in
theorem wkx33_cross_le {n r : ℕ} (G : SimpleGraph (Fin n)) (P : Fin n → Fin r) :
    crossEdges G P ≤ (completePartite P).edgeFinset.card := by
  unfold crossEdges
  apply Finset.card_le_card
  intro e he
  rw [wkx33_mem_inf] at he
  rw [SimpleGraph.mem_edgeFinset]
  exact he.2

theorem wkx33_part_eq {n r : ℕ} (P : Fin n → Fin r) (i : Fin r) :
    part P i = Finset.univ.filter (fun v => P v = i) := by
  ext v; rw [wkx_mem_part]; simp

theorem wkx33_sum_parts {n r : ℕ} (P : Fin n → Fin r) : ∑ i, ((part P i).card : ℝ) = n := by
  have h := Finset.sum_fiberwise (Finset.univ : Finset (Fin n)) P (fun _ => (1:ℝ))
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_univ, Fintype.card_fin] at h
  rw [← h]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [wkx33_part_eq]

open Classical in
theorem wkx33_KP {n r : ℕ} (P : Fin n → Fin r) :
    2 * ((completePartite P).edgeFinset.card : ℝ) =
      (n : ℝ) ^ 2 - ∑ i, ((part P i).card : ℝ) ^ 2 := by
  have h := (completePartite P).sum_degrees_eq_twice_card_edges
  have hdeg : ∀ v, ((completePartite P).degree v : ℝ) = n - ((part P (P v)).card : ℝ) := by
    intro v
    rw [← SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.neighborFinset_eq_filter]
    have hsplit := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin n))) (fun y => (completePartite P).Adj v y)
    rw [Finset.card_univ, Fintype.card_fin] at hsplit
    have he : (Finset.univ.filter (fun y => ¬ (completePartite P).Adj v y)) = part P (P v) := by
      ext y
      rw [Finset.mem_filter, wkx_mem_part]
      simp [completePartite, eq_comm]
    rw [he] at hsplit
    have : (((Finset.univ.filter (fun y => (completePartite P).Adj v y)).card : ℕ) : ℝ) +
        ((part P (P v)).card : ℝ) = n := by exact_mod_cast hsplit
    linarith
  have hsum : ∑ v, ((completePartite P).degree v : ℝ) =
      2 * ((completePartite P).edgeFinset.card : ℝ) := by exact_mod_cast h
  rw [← hsum]
  simp only [hdeg, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  have hfib : ∑ v, ((part P (P v)).card : ℝ) = ∑ i, ((part P i).card : ℝ) ^ 2 := by
    rw [← Finset.sum_fiberwise Finset.univ P (fun v => ((part P (P v)).card : ℝ))]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    have hc : ∀ v ∈ Finset.univ.filter (fun v => P v = i),
        ((part P (P v)).card : ℝ) = (part P i).card := by
      intro v hv
      rw [(Finset.mem_filter.1 hv).2]
    rw [Finset.sum_congr rfl hc, Finset.sum_const, nsmul_eq_mul, ← wkx33_part_eq, sq]
  rw [hfib]
  ring

theorem wkx33_var {r : ℕ} (hr : 0 < r) (x : Fin r → ℝ) (n : ℝ) (hs : ∑ j, x j = n) (i : Fin r) :
    (x i - n / r) ^ 2 ≤ ∑ j, x j ^ 2 - n ^ 2 / r := by
  have h1 : (x i - n / r) ^ 2 ≤ ∑ j, (x j - n / r) ^ 2 :=
    Finset.single_le_sum (f := fun j => (x j - n / r) ^ 2) (fun j _ => sq_nonneg _)
      (Finset.mem_univ i)
  have hrR : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  have h2 : ∑ j, (x j - n / r) ^ 2 = ∑ j, x j ^ 2 - 2 * (n / r) * ∑ j, x j + r * (n / r) ^ 2 := by
    simp only [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Finset.mul_sum]
    congr 1
    congr 1
    refine Finset.sum_congr rfl (fun j _ => ?_)
    ring
  rw [h2, hs] at h1
  have h3 : 2 * (n / r) * n - r * (n / r) ^ 2 = n ^ 2 / r := by
    field_simp
    ring
  linarith

theorem wkx33_iso_label {n r : ℕ} (hr : 0 < r) (H : SimpleGraph (Fin n))
    (φ : H ≃g SimpleGraph.turanGraph n r) :
    H = completePartite (fun v => (⟨((φ v : Fin n) : ℕ) % r, Nat.mod_lt _ hr⟩ : Fin r)) := by
  ext u v
  change H.Adj u v ↔ (_ ≠ _)
  rw [← φ.map_adj_iff, SimpleGraph.turanGraph_adj]
  simp [Fin.ext_iff]

theorem wkx33_not_col {W : Type*} [Fintype W] (F : SimpleGraph W) (r n : ℕ) (hr : 0 < r)
    (hn : r * Fintype.card W ≤ n) (hfree : F.Free (SimpleGraph.turanGraph n r)) :
    ¬ F.Colorable r := by
  rintro ⟨c⟩
  apply hfree
  let e := Fintype.equivFin W
  have hlt : ∀ p, ((c p : Fin r) : ℕ) + r * (e p : ℕ) < n := by
    intro p
    have h1 := (c p).isLt
    have h2 := (e p).isLt
    have h3 : r * ((e p : ℕ) + 1) ≤ r * Fintype.card W := Nat.mul_le_mul_left _ h2
    rw [mul_add, mul_one] at h3
    omega
  refine ⟨⟨⟨fun p => ⟨(c p : ℕ) + r * (e p : ℕ), hlt p⟩, ?_⟩, ?_⟩⟩
  · intro p q hpq
    rw [SimpleGraph.turanGraph_adj]
    simp only
    rw [Nat.add_mul_mod_self_left, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (c p).isLt,
      Nat.mod_eq_of_lt (c q).isLt]
    intro h
    exact c.valid hpq (Fin.ext h)
  · intro p q hpq
    simp only [RelHom.coeFn_mk, Fin.mk.injEq] at hpq
    have h1 := congrArg (· % r) hpq
    have h2 := congrArg (· / r) hpq
    simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (c p).isLt,
      Nat.mod_eq_of_lt (c q).isLt] at h1
    simp only [Nat.add_mul_div_left _ _ hr, Nat.div_eq_of_lt (c p).isLt,
      Nat.div_eq_of_lt (c q).isLt, zero_add] at h2
    exact e.injective (Fin.ext h2)

theorem wkx33_col {W : Type*} [Fintype W] (F : SimpleGraph W) (n r : ℕ)
    (hfree : ¬ F.Colorable (r + 1)) : F.Free (SimpleGraph.turanGraph n (r + 1)) := by
  rintro ⟨f⟩
  apply hfree
  refine ⟨SimpleGraph.Coloring.mk
    (fun p => (⟨((f.toHom p : Fin n) : ℕ) % (r + 1), Nat.mod_lt _ (by omega)⟩ : Fin (r + 1))) ?_⟩
  intro p q hpq heq
  have h := f.toHom.map_adj hpq
  rw [SimpleGraph.turanGraph_adj] at h
  exact h (by simpa using congrArg Fin.val heq)

theorem wkx33_num {n r a : ℕ} (hr : 2 ≤ r) (e0 e1 : ℝ)
    (hn : (r : ℝ) * (r + 1) * (2 * a + 2) ≤ n)
    (h1 : (n : ℝ) * ((n : ℝ) - n / ((r : ℝ) + 1) - 1) ≤ 2 * e1)
    (h0 : 2 * r * e0 ≤ ((r : ℝ) - 1) * n ^ 2) (h01 : e1 ≤ e0 + a) : False := by
  have hrR : (2 : ℝ) ≤ r := by exact_mod_cast hr
  set q := (n : ℝ) / ((r : ℝ) + 1) with hqdef
  have hq : q * ((r : ℝ) + 1) = n := by rw [hqdef]; field_simp
  have hs0 : (0 : ℝ) ≤ (r : ℝ) * (r + 1) := by positivity
  have hA := mul_le_mul_of_nonneg_left h1 hs0
  have hq2 : (r : ℝ) * (r + 1) * n * q = r * n * n := by
    rw [show (r : ℝ) * (r + 1) * n * q = r * n * (q * (r + 1)) by ring, hq]
  have ha0 : (0 : ℝ) ≤ a := by positivity
  have hn1 : (1 : ℝ) ≤ n := by nlinarith
  -- n (n - s) ≥ n * s * (2a+1) ≥ s (2a+1)
  have hB : (n : ℝ) * (n - r * (r + 1)) ≥ (r * (r + 1)) * (2 * a + 1) := by
    have h5 : (n : ℝ) - r * (r + 1) ≥ (r * (r + 1)) * (2 * a + 1) := by nlinarith
    have h6 : (0 : ℝ) ≤ (r * (r + 1)) * (2 * a + 1) := by positivity
    nlinarith
  nlinarith

open Classical in
theorem wkx33_Tfree {W : Type*} [Fintype W] (F : SimpleGraph W) (r a : ℕ) (hr : 2 ≤ r)
    (hF : TuranPlusEdges F r a) :
    ∃ N : ℕ, ∀ n ≥ N, F.Free (SimpleGraph.turanGraph n r) := by
  obtain ⟨N0, hN0⟩ := hF
  by_cases hbot : F = ⊥
  · exfalso
    set n := N0 + Fintype.card W + 2 with hn
    have hle : SimpleGraph.extremalNumber n F ≤ 0 := by
      have := (SimpleGraph.extremalNumber_le_iff (V := Fin n) F 0).2 (by
        intro G _ hG
        exfalso
        apply hG
        obtain ⟨emb⟩ : Nonempty (W ↪ Fin n) :=
          Function.Embedding.nonempty_of_card_le (by simp; omega)
        refine ⟨⟨⟨emb, ?_⟩, emb.injective⟩⟩
        intro p q hpq
        rw [hbot] at hpq
        exact absurd hpq (by simp))
      simpa using this
    have hT := (hN0 n (by omega)).1
    have hmem : s(⟨0, by omega⟩, ⟨1, by omega⟩) ∈ (SimpleGraph.turanGraph n r).edgeFinset := by
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, SimpleGraph.turanGraph_adj]
      simp only
      rw [Nat.zero_mod, Nat.mod_eq_of_lt (show 1 < r by omega)]
      omega
    have hpos := Finset.card_pos.2 ⟨_, hmem⟩
    omega
  · refine ⟨N0, fun n hn => ?_⟩
    have hb : F.Free (⊥ : SimpleGraph (Fin n)) := SimpleGraph.free_bot hbot
    obtain ⟨Hx, hHfree, hHcard⟩ := wkx_exists_extremal F ⊥ hb
    exact fun hc => hHfree (hc.trans ((hN0 n hn).2 Hx hHfree hHcard))

open Classical in
theorem wkx33_chi {W : Type*} [Fintype W] (F : SimpleGraph W) (r a : ℕ) (hr : 2 ≤ r)
    (hF : TuranPlusEdges F r a) : F.chromaticNumber = ((r + 1 : ℕ) : ℕ∞) := by
  obtain ⟨N1, hN1⟩ := wkx33_Tfree F r a hr hF
  obtain ⟨N0, hN0⟩ := hF
  rw [Nat.cast_add, Nat.cast_one, SimpleGraph.chromaticNumber_eq_iff_colorable_not_colorable]
  refine ⟨?_, wkx33_not_col F r (r * Fintype.card W + N1) (by omega) (by omega)
    (hN1 _ (by omega))⟩
  by_contra hnc
  set n := r * (r + 1) * (2 * a + 2) * (N0 + 1) with hn
  have hn1 : r * (r + 1) * (2 * a + 2) ≤ n := Nat.le_mul_of_pos_right _ (by omega)
  have hnN : N0 ≤ n := by
    have : 1 ≤ r * (r + 1) * (2 * a + 2) := Nat.one_le_iff_ne_zero.2 (by positivity)
    calc N0 ≤ N0 + 1 := by omega
      _ = 1 * (N0 + 1) := by ring
      _ ≤ r * (r + 1) * (2 * a + 2) * (N0 + 1) := Nat.mul_le_mul_right _ this
  have hfr := wkx33_col F n r hnc
  have hle := SimpleGraph.card_edgeFinset_le_extremalNumber hfr
  rw [Fintype.card_fin, (hN0 n hnN).1] at hle
  have hlow := wkx33_turan_edges (n := n) (r := r + 1) (by omega) (SimpleGraph.turanGraph n (r + 1))
    (fun u w => SimpleGraph.turanGraph_adj)
  have hup := SimpleGraph.mul_card_edgeFinset_turanGraph_le (n := n) (r := r)
  apply wkx33_num (n := n) (r := r) (a := a) hr
    ((SimpleGraph.turanGraph n r).edgeFinset.card : ℝ)
    ((SimpleGraph.turanGraph n (r + 1)).edgeFinset.card : ℝ)
  · exact_mod_cast hn1
  · convert hlow using 3
    · push_cast; ring
    · exact wkx33_card_inst _ _ _
  · have : ((2 * r * (SimpleGraph.turanGraph n r).edgeFinset.card : ℕ) : ℝ) ≤
        (((r - 1) * n ^ 2 : ℕ) : ℝ) := by exact_mod_cast hup
    push_cast [Nat.cast_sub (show 1 ≤ r by omega)] at this
    convert this using 2
  · have : (((SimpleGraph.turanGraph n (r + 1)).edgeFinset.card : ℕ) : ℝ) ≤
        (((SimpleGraph.turanGraph n r).edgeFinset.card + a : ℕ) : ℝ) := by
      exact_mod_cast (by convert hle)
    push_cast at this
    exact this

open Classical in
theorem wkx33_final {W : Type*} [Fintype W] (F : SimpleGraph W) (r a : ℕ) (hr : 2 ≤ r)
    (hF : TuranPlusEdges F r a)
    (hcor : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ G : SimpleGraph (Fin n),
      F.Free G → (1 - 1 / (r : ℝ) - δ) * n ≤ specRad G →
      ∃ H : SimpleGraph (Fin n), Nonempty (H ≃g SimpleGraph.turanGraph n r) ∧
        ((G.edgeFinset \ H.edgeFinset).card + (H.edgeFinset \ G.edgeFinset).card : ℝ) ≤
          ε * (n : ℝ) ^ 2) :
    ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ G : SimpleGraph (Fin n), IsSpectralExtremal F G →
      ((SimpleGraph.turanGraph n r).edgeFinset.card - ε * (n : ℝ) ^ 2 ≤ G.edgeFinset.card) ∧
      ∀ P : Fin n → Fin r, IsMaxCut G P →
        ((∑ i, edgesIn G (part P i) : ℕ) : ℝ) ≤ ε * (n : ℝ) ^ 2 ∧
        ∀ i : Fin r,
          (1 / (r : ℝ) - 3 * Real.sqrt ε) * n < (part P i).card ∧
          ((part P i).card : ℝ) < (1 / (r : ℝ) + 3 * Real.sqrt ε) * n := by
  intro ε hε
  obtain ⟨δ, hδ, n₁, hn₁⟩ := hcor (ε / 2) (by linarith)
  obtain ⟨N0, hN0⟩ := wkx33_Tfree F r a hr hF
  obtain ⟨K, hK⟩ := exists_nat_gt (1 / δ + 1 / ε)
  refine ⟨N0 + n₁ + K + 1, fun n hn G hG => ?_⟩
  obtain ⟨hfree, hmax⟩ := hG
  have hr0 : 0 < r := by omega
  have hnpos : 0 < n := by omega
  have hnR : (0:ℝ) < n := by exact_mod_cast hnpos
  have hKn : (K : ℝ) + 1 ≤ n := by exact_mod_cast (show K + 1 ≤ n by omega)
  have hpδ := one_div_pos.2 hδ
  have hpε := one_div_pos.2 hε
  have h1δ : 1 / δ < n := by linarith
  have h1ε : 1 / ε < n := by linarith
  have hδn : 1 < n * δ := by rwa [div_lt_iff₀ hδ] at h1δ
  have hεn : 1 < n * ε := by rwa [div_lt_iff₀ hε] at h1ε
  have hTfree := hN0 n (by omega)
  have hlamT := wkx33_turan_lam hr0 hnpos (SimpleGraph.turanGraph n r)
    (fun u w => SimpleGraph.turanGraph_adj)
  have hlam : (1 - 1 / (r : ℝ) - δ) * n ≤ specRad G := by
    have := hmax _ hTfree
    linarith
  obtain ⟨H, ⟨φ⟩, hHG⟩ := hn₁ n (by omega) G hfree hlam
  have eH : (H.edgeFinset.card : ℝ) = (SimpleGraph.turanGraph n r).edgeFinset.card := by
    have := φ.card_edgeFinset_eq
    exact_mod_cast this
  have hGH0 : (0 : ℝ) ≤ (G.edgeFinset \ H.edgeFinset).card := by positivity
  have hHG0 : (0 : ℝ) ≤ (H.edgeFinset \ G.edgeFinset).card := by positivity
  have hεn2 : 0 ≤ ε * (n : ℝ) ^ 2 := by positivity
  set Q : Fin n → Fin r := fun v => ⟨((φ v : Fin n) : ℕ) % r, Nat.mod_lt _ hr0⟩ with hQ
  have hHQ : H = completePartite Q := wkx33_iso_label hr0 H φ
  have hmem : ∀ e, e ∈ (completePartite Q).edgeSet ↔ e ∈ H.edgeSet := by
    rw [← hHQ]; exact fun e => Iff.rfl
  have hs1 : crossEdges G Q + (G.edgeFinset \ H.edgeFinset).card = G.edgeFinset.card := by
    unfold crossEdges
    apply wkx33_cardsplit _ _ _ (fun e => e ∈ H.edgeSet)
    · intro e
      rw [wkx33_mem_inf, hmem, SimpleGraph.mem_edgeFinset]
    · intro e
      rw [Finset.mem_sdiff, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeFinset]
  have hs2 : crossEdges G Q + (H.edgeFinset \ G.edgeFinset).card = H.edgeFinset.card := by
    unfold crossEdges
    apply wkx33_cardsplit _ _ _ (fun e => e ∈ G.edgeSet)
    · intro e
      rw [wkx33_mem_inf, hmem, SimpleGraph.mem_edgeFinset]
      exact and_comm
    · intro e
      rw [Finset.mem_sdiff, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeFinset]
  have hs1R : (crossEdges G Q : ℝ) + (G.edgeFinset \ H.edgeFinset).card = G.edgeFinset.card := by
    exact_mod_cast hs1
  have hs2R : (crossEdges G Q : ℝ) + (H.edgeFinset \ G.edgeFinset).card = H.edgeFinset.card := by
    exact_mod_cast hs2
  refine ⟨by linarith, fun P hP => ?_⟩
  have hcrossR : (crossEdges G Q : ℝ) ≤ crossEdges G P := by exact_mod_cast hP Q
  have hinR : ((∑ i, edgesIn G (part P i) : ℕ) : ℝ) + (crossEdges G P : ℝ) ≤
      G.edgeFinset.card := by exact_mod_cast wkx33_in_cross G P
  refine ⟨by linarith, fun i => ?_⟩
  have hKPR : (crossEdges G P : ℝ) ≤ (completePartite P).edgeFinset.card := by
    exact_mod_cast wkx33_cross_le G P
  have hKP2 := wkx33_KP P
  have hTe := wkx33_turan_edges hr0 (SimpleGraph.turanGraph n r)
    (fun u w => SimpleGraph.turanGraph_adj)
  have hTe' : (n : ℝ) * ((n : ℝ) - n / r - 1) ≤
      2 * ((SimpleGraph.turanGraph n r).edgeFinset.card : ℝ) := by
    convert hTe using 3
    exact wkx33_card_inst _ _ _
  have e1 : (n : ℝ) * ((n : ℝ) - n / r - 1) = n ^ 2 - n ^ 2 / r - n := by ring
  have hsq : ∑ j, ((part P j).card : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 / r + n + ε * n ^ 2 := by
    linarith
  have hvar := wkx33_var hr0 (fun j => ((part P j).card : ℝ)) n (wkx33_sum_parts P) i
  have hsqrt : (3 * Real.sqrt ε * n) ^ 2 = 9 * ε * n ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt hε.le]; ring
  have hnε : (n : ℝ) < ε * n ^ 2 := by
    have := mul_lt_mul_of_pos_left hεn hnR
    linarith
  have hlt : (((part P i).card : ℝ) - n / r) ^ 2 < (3 * Real.sqrt ε * n) ^ 2 := by
    rw [hsqrt]
    linarith
  have hb : 0 ≤ 3 * Real.sqrt ε * n := by positivity
  have hab := abs_lt_of_sq_lt_sq' hlt hb
  have e2 : (1 / (r : ℝ)) * n = n / r := by ring
  constructor <;> linarith [hab.1, hab.2]

end WKX33

-- Lemma 3.3 (Wang-Kang-Xue) by reduction to Corollary 2.6 (spectral stability).
open WangKangXue.SpectralTuran Classical in
theorem solution {W : Type*} [Fintype W] (F : SimpleGraph W) (r a : ℕ) (hr : 2 ≤ r)
    (hF : TuranPlusEdges F r a) :
    ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ G : SimpleGraph (Fin n), IsSpectralExtremal F G →
      ((SimpleGraph.turanGraph n r).edgeFinset.card - ε * (n : ℝ) ^ 2 ≤ G.edgeFinset.card) ∧
      ∀ P : Fin n → Fin r, IsMaxCut G P →
        ((∑ i, edgesIn G (part P i) : ℕ) : ℝ) ≤ ε * (n : ℝ) ^ 2 ∧
        ∀ i : Fin r,
          (1 / (r : ℝ) - 3 * Real.sqrt ε) * n < (part P i).card ∧
          ((part P i).card : ℝ) < (1 / (r : ℝ) + 3 * Real.sqrt ε) * n := by
  exact wkx33_final F r a hr hF (corollary_2_6 F r hr (wkx33_chi F r a hr hF))
