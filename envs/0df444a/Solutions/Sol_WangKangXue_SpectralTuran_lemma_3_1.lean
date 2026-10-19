-- Prove2me | solution 1 for WangKangXue.SpectralTuran.lemma_3_1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-16T23:17:41.698841+00:00
-- url     : https://prove2.me/submissions/31ef31e4-e1c1-4cc1-b25b-7f64a6e34ff7

import Mathlib
import Definitions.Def_WangKangXue_SpectralTuran_specRad
import Definitions.Def_WangKangXue_SpectralTuran_IsSpectralExtremal
import Definitions.Def_WangKangXue_SpectralTuran_TuranPlusEdges

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




section WKX31

open WangKangXue.SpectralTuran

open Classical in
theorem wkx_exists_extremal {W : Type*} (F : SimpleGraph W) {n : ℕ} (G : SimpleGraph (Fin n))
    (hG : F.Free G) :
    ∃ H : SimpleGraph (Fin n), F.Free H ∧ H.edgeFinset.card = SimpleGraph.extremalNumber n F := by
  obtain ⟨H, inst, hH⟩ := (SimpleGraph.exists_isExtremal_iff_exists F.Free).2 ⟨G, hG⟩
  rw [SimpleGraph.isExtremal_free_iff, Fintype.card_fin] at hH
  exact ⟨H, hH.1, by convert hH.2⟩


open Classical in
/-- Non-adjacency classes of `T_{n,r}` have sizes differing by at most one. -/
theorem wkx_turan_class_balanced {n r : ℕ} (hr : 0 < r) (z w : Fin n) :
    (Finset.univ.filter (fun y => ¬ (SimpleGraph.turanGraph n r).Adj z y)).card ≤
      (Finset.univ.filter (fun y => ¬ (SimpleGraph.turanGraph n r).Adj w y)).card + 1 := by
  have h := SimpleGraph.isTuranMaximal_turanGraph (n := n) hr
  have hc : ∀ x : Fin n, (Finset.univ.filter (fun y => ¬ (SimpleGraph.turanGraph n r).Adj x y)) =
      h.finpartition.part x := by
    intro x
    ext y
    rw [Finset.mem_filter, h.finpartition.mem_part_iff_part_eq_part (Finset.mem_univ y)
      (Finset.mem_univ x), h.not_adj_iff_part_eq]
    simp [eq_comm]
  rw [hc, hc]
  exact h.isEquipartition (h.finpartition.part_mem.2 (Finset.mem_univ z))
    (h.finpartition.part_mem.2 (Finset.mem_univ w))


open Classical in
/-- Class balance transported to any graph with Turán adjacency. -/
theorem wkx_class_balanced_of {n r : ℕ} (hr : 0 < r) (T : SimpleGraph (Fin n))
    (hTadj : ∀ u w, T.Adj u w ↔ (u : ℕ) % r ≠ (w : ℕ) % r) (z w : Fin n) :
    ((Finset.univ.filter (fun y => ¬ T.Adj z y)).card : ℝ) ≤
      ((Finset.univ.filter (fun y => ¬ T.Adj w y)).card : ℝ) + 1 := by
  classical
  have h := wkx_turan_class_balanced (n := n) hr z w
  have e : ∀ x : Fin n, (Finset.univ.filter (fun y => ¬ T.Adj x y)).card =
      (Finset.univ.filter (fun y => ¬ (SimpleGraph.turanGraph n r).Adj x y)).card := by
    intro x
    congr 1
    refine Finset.filter_congr (fun y _ => ?_)
    rw [hTadj, SimpleGraph.turanGraph_adj]
  rw [e, e]
  exact_mod_cast h


open Classical Matrix in
theorem wkx37_rayleigh {n : ℕ} (H : SimpleGraph (Fin n)) (hn : 0 < n) (y : Fin n → ℝ) :
    y ⬝ᵥ (H.adjMatrix ℝ *ᵥ y) ≤ specRad H * (y ⬝ᵥ y) := by
  have hn0 : 0 < Fintype.card (Fin n) := by simpa using hn
  have hs : specRad H = (H.isHermitian_adjMatrix ℝ).eigenvalues₀ ⟨0, hn0⟩ := by
    unfold specRad; rw [dif_pos hn0]
  rw [hs]
  exact wk9_le (H.isHermitian_adjMatrix ℝ) hn0 y


open Classical Matrix in
theorem wkx31_nonneg_eig {n : ℕ} (G : SimpleGraph (Fin n)) (hn : 0 < n) :
    ∃ y : Fin n → ℝ, y ⬝ᵥ y = 1 ∧ G.adjMatrix ℝ *ᵥ y = specRad G • y ∧ ∀ i, 0 ≤ y i := by
  have hn0 : 0 < Fintype.card (Fin n) := by simpa using hn
  obtain ⟨x, hxx, hx⟩ := wk9_exists (G.isHermitian_adjMatrix ℝ) hn0
  have hs : specRad G = (G.isHermitian_adjMatrix ℝ).eigenvalues₀ ⟨0, hn0⟩ := by
    unfold specRad; rw [dif_pos hn0]
  rw [← hs] at hx
  obtain ⟨y, hy⟩ : ∃ y : Fin n → ℝ, y = fun i => |x i| := ⟨_, rfl⟩
  have hyy : y ⬝ᵥ y = 1 := by
    rw [← hxx]
    unfold dotProduct
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [hy]
    exact abs_mul_abs_self (x i)
  have hq : x ⬝ᵥ (G.adjMatrix ℝ *ᵥ x) ≤ y ⬝ᵥ (G.adjMatrix ℝ *ᵥ y) := by
    rw [wk9_quad, wk9_quad]
    refine Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => ?_))
    split_ifs
    · rw [hy, ← abs_mul]
      exact le_abs_self _
    · exact le_rfl
  have hxq : x ⬝ᵥ (G.adjMatrix ℝ *ᵥ x) = specRad G := by
    rw [hx, dotProduct_smul, smul_eq_mul, hxx, mul_one]
  have hR := wkx37_rayleigh G hn
  have heq : y ⬝ᵥ (G.adjMatrix ℝ *ᵥ y) = specRad G * (y ⬝ᵥ y) := by
    have h1 := hR y
    rw [hyy] at h1 ⊢
    linarith
  refine ⟨y, hyy, wk9_eq _ (wk9_transpose (G.isHermitian_adjMatrix ℝ)) _ hR y heq, ?_⟩
  intro i
  rw [hy]
  exact abs_nonneg _

open Classical Matrix in
theorem wkx31_deg {n : ℕ} (G : SimpleGraph (Fin n)) (y : Fin n → ℝ) (lam : ℝ)
    (hev : G.adjMatrix ℝ *ᵥ y = lam • y) (u : Fin n) (hu : 0 < y u)
    (hmax : ∀ i, y i ≤ y u) :
    lam ≤ (G.degree u : ℝ) := by
  have h := congrFun hev u
  rw [wk9_row, Pi.smul_apply, smul_eq_mul] at h
  have h2 : (∑ j, (if G.Adj u j then y j else 0)) ≤ ∑ j, (if G.Adj u j then y u else 0) :=
    Finset.sum_le_sum (fun j _ => by split_ifs; exacts [hmax j, le_rfl])
  have hc : (Finset.univ.filter (fun j => G.Adj u j)).card = G.degree u := by
    rw [← G.card_neighborFinset_eq_degree]
    congr 1
    ext j
    simp
  have hc2 : (∑ j, (if G.Adj u j then y u else 0)) = (G.degree u : ℝ) * y u := by
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, hc]
  rw [hc2, h] at h2
  exact le_of_mul_le_mul_right h2 hu

open Classical Matrix in
theorem wkx31_restrict {n : ℕ} (G : SimpleGraph (Fin n)) (y : Fin n → ℝ) (lam : ℝ)
    (hev : G.adjMatrix ℝ *ᵥ y = lam • y) (u : Fin n) :
    G.adjMatrix ℝ *ᵥ (fun i => if G.Reachable u i then y i else 0) =
      lam • (fun i => if G.Reachable u i then y i else 0) := by
  funext i
  have h := congrFun hev i
  rw [wk9_row, Pi.smul_apply, smul_eq_mul] at h
  rw [wk9_row, Pi.smul_apply, smul_eq_mul]
  by_cases hi : G.Reachable u i
  · rw [if_pos hi, ← h]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    by_cases hij : G.Adj i j
    · rw [if_pos hij, if_pos hij, if_pos (hi.trans hij.reachable)]
    · rw [if_neg hij, if_neg hij]
  · rw [if_neg hi, mul_zero]
    refine Finset.sum_eq_zero (fun j _ => ?_)
    by_cases hij : G.Adj i j
    · rw [if_pos hij, if_neg (fun hj => hi (hj.trans hij.symm.reachable))]
    · rw [if_neg hij]

open Classical Matrix in
theorem wkx31_gain {n : ℕ} (G H : SimpleGraph (Fin n)) (y : Fin n → ℝ) (lam : ℝ)
    (hev : G.adjMatrix ℝ *ᵥ y = lam • y) (u w : Fin n) (huw : u ≠ w) (hu : 0 < y u)
    (hw : y w = 0)
    (hH : ∀ i j, H.Adj i j ↔ (G.Adj i j ∧ i ≠ w ∧ j ≠ w) ∨ (i = w ∧ j = u) ∨ (i = u ∧ j = w)) :
    lam < specRad H := by
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = y u / (|lam| + 1) := ⟨_, rfl⟩
  obtain ⟨z, hz⟩ : ∃ z : Fin n → ℝ, z = fun i => if i = w then t else y i := ⟨_, rfl⟩
  have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) u.isLt
  have hR := wkx37_rayleigh H hn z
  have hterm : ∀ i j, (if H.Adj i j then z i * z j else 0) =
      (if G.Adj i j then y i * y j else 0) +
        ((if i = w ∧ j = u then t * y u else 0) + (if i = u ∧ j = w then t * y u else 0)) := by
    intro i j
    rw [hH i j, hz]
    by_cases hi : i = w
    · subst hi
      by_cases hj : j = u
      · subst hj
        simp [huw, Ne.symm huw, hw]
      · simp [hj, hw, Ne.symm huw]
    · by_cases hj : j = w
      · subst hj
        by_cases hiu : i = u
        · subst hiu
          simp [huw, hw]
          ring
        · simp [hi, hiu, hw]
      · simp [hi, hj]
  have hQ : z ⬝ᵥ (H.adjMatrix ℝ *ᵥ z) = y ⬝ᵥ (G.adjMatrix ℝ *ᵥ y) + 2 * (t * y u) := by
    rw [wk9_quad, wk9_quad]
    simp_rw [hterm, Finset.sum_add_distrib]
    simp [ite_and, huw]
    ring
  have hzz : z ⬝ᵥ z = y ⬝ᵥ y + t ^ 2 := by
    have hzi : ∀ i, z i * z i = y i * y i + (if i = w then t ^ 2 else 0) := by
      intro i
      rw [hz]
      by_cases hi : i = w
      · subst hi; simp [hw]; ring
      · simp [hi]
    unfold dotProduct
    simp_rw [hzi, Finset.sum_add_distrib]
    simp
  have hy : y ⬝ᵥ (G.adjMatrix ℝ *ᵥ y) = lam * (y ⬝ᵥ y) := by
    rw [hev, dotProduct_smul, smul_eq_mul]
  have hY : 0 ≤ y ⬝ᵥ y := Finset.sum_nonneg (fun i _ => mul_self_nonneg (y i))
  have hl1 : 0 < |lam| + 1 := by positivity
  have htpos : 0 < t := by rw [ht]; positivity
  have htl : t * (|lam| + 1) = y u := by rw [ht]; field_simp
  by_contra hcon
  push_neg at hcon
  rw [hQ, hy, hzz] at hR
  have h1 : specRad H * (y ⬝ᵥ y + t ^ 2) ≤ lam * (y ⬝ᵥ y + t ^ 2) :=
    mul_le_mul_of_nonneg_right hcon (by positivity)
  have h2 : 2 * (t * y u) ≤ lam * t ^ 2 := by nlinarith
  have h3 : lam * t ^ 2 ≤ |lam| * t ^ 2 :=
    mul_le_mul_of_nonneg_right (le_abs_self lam) (by positivity)
  have h4 : 2 * y u ≤ |lam| * t := by
    have : t * (2 * y u) ≤ t * (|lam| * t) := by nlinarith
    exact le_of_mul_le_mul_left this htpos
  nlinarith [abs_nonneg lam]

theorem wkx31_free {W : Type*} [Fintype W] (F : SimpleGraph W) {n : ℕ}
    (G H : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hF : F.Free G) (u w : Fin n) (huw : u ≠ w) (hGuw : ¬ G.Adj u w)
    (hdeg : Fintype.card W ≤ G.degree u)
    (hH : ∀ i j, H.Adj i j ↔ (G.Adj i j ∧ i ≠ w ∧ j ≠ w) ∨ (i = w ∧ j = u) ∨ (i = u ∧ j = w)) :
    F.Free H := by
  classical
  rintro ⟨f⟩
  apply hF
  by_cases hp : ∃ p q, f.toHom p = w ∧ F.Adj p q
  · obtain ⟨p, q, hpw, hpq⟩ := hp
    have hnb : ∀ q', F.Adj p q' → f.toHom q' = u := by
      intro q' hq'
      have h := f.toHom.map_adj hq'
      rw [hH, hpw] at h
      rcases h with ⟨-, h, -⟩ | ⟨-, h⟩ | ⟨h, -⟩
      · exact absurd rfl h
      · exact h
      · exact absurd h.symm huw
    have hq : f.toHom q = u := hnb q hpq
    have huniq : ∀ q', F.Adj p q' → q' = q := fun q' hq' =>
      f.injective ((hnb q' hq').trans hq.symm)
    -- a neighbour of u outside the image of f
    obtain ⟨z, hzN, hzX⟩ : ∃ z, G.Adj u z ∧ ∀ x, f.toHom x ≠ z := by
      by_contra hc
      push_neg at hc
      have hsub : G.neighborFinset u ⊆ (Finset.univ.image f.toHom).erase w := by
        intro z hz
        rw [SimpleGraph.mem_neighborFinset] at hz
        obtain ⟨x, hx⟩ := hc z hz
        refine Finset.mem_erase.2 ⟨?_, ?_⟩
        · rintro rfl
          exact hGuw hz
        · exact hx ▸ Finset.mem_image_of_mem _ (Finset.mem_univ x)
      have hw_mem : w ∈ Finset.univ.image f.toHom := hpw ▸ Finset.mem_image_of_mem _ (Finset.mem_univ p)
      have h1 := Finset.card_le_card hsub
      rw [Finset.card_erase_of_mem hw_mem, Finset.card_image_of_injective _ f.injective,
        Finset.card_univ, SimpleGraph.card_neighborFinset_eq_degree] at h1
      have hpos : 0 < Fintype.card W := Fintype.card_pos_iff.2 ⟨p⟩
      omega
    refine ⟨⟨⟨fun x => if x = p then z else f.toHom x, ?_⟩, ?_⟩⟩
    · intro a b hab
      change G.Adj (if a = p then z else f.toHom a) (if b = p then z else f.toHom b)
      split_ifs with h1 h2 h2
      · exact absurd (h1.trans h2.symm) (F.ne_of_adj hab)
      · subst h1
        rw [huniq b hab, hq]
        exact hzN.symm
      · subst h2
        rw [huniq a hab.symm, hq]
        exact hzN
      · have h := f.toHom.map_adj hab
        rw [hH] at h
        have ha : f.toHom a ≠ w := fun e => h1 (f.injective (e.trans hpw.symm))
        have hb : f.toHom b ≠ w := fun e => h2 (f.injective (e.trans hpw.symm))
        rcases h with ⟨h, -, -⟩ | ⟨h, -⟩ | ⟨-, h⟩
        · exact h
        · exact absurd h ha
        · exact absurd h hb
    · intro a b hab
      change (if a = p then z else f.toHom a) = (if b = p then z else f.toHom b) at hab
      split_ifs at hab with h1 h2 h2
      · exact h1.trans h2.symm
      · exact absurd hab.symm (hzX b)
      · exact absurd hab (hzX a)
      · exact f.injective hab
  · push_neg at hp
    refine ⟨⟨⟨fun x => f.toHom x, ?_⟩, ?_⟩⟩
    · intro a b hab
      have h := f.toHom.map_adj hab
      rw [hH] at h
      rcases h with ⟨h, -, -⟩ | ⟨h, -⟩ | ⟨-, h⟩
      · exact h
      · exact absurd hab (hp a b h)
      · exact absurd hab.symm (hp b a h)
    · intro a b hab
      exact f.injective hab

open Classical Matrix in
theorem wkx31_turan_lower {n r : ℕ} (hr : 2 ≤ r) (hn : 2 ≤ n) (T : SimpleGraph (Fin n))
    (hTadj : ∀ u w, T.Adj u w ↔ (u : ℕ) % r ≠ (w : ℕ) % r) :
    ((n : ℝ) - 1) / 2 ≤ specRad T := by
  have hR := wkx37_rayleigh T (by omega) (fun _ : Fin n => (1 : ℝ))
  rw [wk9_quad] at hR
  beta_reduce at hR
  have h11 : ((fun _ : Fin n => (1 : ℝ)) ⬝ᵥ (fun _ : Fin n => (1 : ℝ)) : ℝ) = n := by
    simp [dotProduct]
  rw [h11] at hR
  have hrow : ∀ i : Fin n, ((n : ℝ) - 1) / 2 ≤
      ∑ j, (if T.Adj i j then (1 : ℝ) * 1 else 0) := by
    intro i
    obtain ⟨k, hk⟩ : ∃ k : Fin n, T.Adj i k := by
      have h1r : (1 : ℕ) % r = 1 := Nat.mod_eq_of_lt (by omega)
      by_cases h0 : (i : ℕ) % r = 0
      · refine ⟨⟨1, by omega⟩, (hTadj _ _).2 ?_⟩
        simp only [h1r, h0]
        omega
      · refine ⟨⟨0, by omega⟩, (hTadj _ _).2 ?_⟩
        simpa using h0
    have hbal := wkx_class_balanced_of (by omega) T hTadj i k
    have hdisj : Disjoint (Finset.univ.filter (fun y => ¬ T.Adj i y))
        (Finset.univ.filter (fun y => ¬ T.Adj k y)) := by
      rw [Finset.disjoint_filter]
      intro y _ h1 h2
      rw [hTadj] at h1 h2 hk
      push_neg at h1 h2
      exact hk (h1.trans h2.symm)
    have hU := Finset.card_union_of_disjoint hdisj
    have hUle : (Finset.univ.filter (fun y => ¬ T.Adj i y) ∪
        Finset.univ.filter (fun y => ¬ T.Adj k y)).card ≤ n := by
      simpa using Finset.card_le_univ (Finset.univ.filter (fun y => ¬ T.Adj i y) ∪
        Finset.univ.filter (fun y => ¬ T.Adj k y))
    have hsplit := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin n))) (fun y => T.Adj i y)
    rw [Finset.card_univ, Fintype.card_fin] at hsplit
    have hs : (∑ j, (if T.Adj i j then (1 : ℝ) * 1 else 0)) =
        ((Finset.univ.filter (fun y => T.Adj i y)).card : ℝ) := by
      rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul,
        mul_one, mul_one]
    rw [hs]
    have hUR : ((Finset.univ.filter (fun y => ¬ T.Adj i y)).card : ℝ) +
        ((Finset.univ.filter (fun y => ¬ T.Adj k y)).card : ℝ) ≤ n := by
      rw [hU] at hUle
      exact_mod_cast hUle
    have hsR : ((Finset.univ.filter (fun y => T.Adj i y)).card : ℝ) +
        ((Finset.univ.filter (fun y => ¬ T.Adj i y)).card : ℝ) = n := by
      exact_mod_cast hsplit
    linarith
  have hsum : (n : ℝ) * (((n : ℝ) - 1) / 2) ≤
      ∑ i, ∑ j, (if T.Adj i j then (1 : ℝ) * 1 else 0) := by
    have := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hrow i)
    simpa using this
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hfin : (n : ℝ) * (((n : ℝ) - 1) / 2) ≤ specRad T * n :=
    le_trans hsum (by convert hR using 1)
  by_contra hlt
  have := mul_lt_mul_of_pos_right (not_le.1 hlt) hnR
  linarith

end WKX31

-- Lemma 3.1 (Wang–Kang–Xue): for large n every spectral-extremal F-free graph is connected.
open WangKangXue.SpectralTuran Classical in
theorem solution {W : Type*} [Fintype W] (F : SimpleGraph W) (r a : ℕ) (hr : 2 ≤ r)
    (hF : TuranPlusEdges F r a) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ G : SimpleGraph (Fin n), IsSpectralExtremal F G → G.Connected := by
  obtain ⟨N0, hN0⟩ := hF
  refine ⟨N0 + 2 * Fintype.card W + 2, fun n hn G hG => ?_⟩
  obtain ⟨hfree, hmax⟩ := hG
  have hn2 : 2 ≤ n := by omega
  have hnpos : 0 < n := by omega
  obtain ⟨Hx, hHfree, hHcard⟩ := wkx_exists_extremal F G hfree
  have hTc := (hN0 n (by omega)).2 Hx hHfree hHcard
  have hTfree : F.Free (SimpleGraph.turanGraph n r) := fun hc => hHfree (hc.trans hTc)
  have hlamT := wkx31_turan_lower hr hn2 (SimpleGraph.turanGraph n r)
    (fun u w => SimpleGraph.turanGraph_adj)
  have hlam : ((n : ℝ) - 1) / 2 ≤ specRad G := le_trans hlamT (hmax _ hTfree)
  obtain ⟨y, hyy, hev, hy0⟩ := wkx31_nonneg_eig G hnpos
  obtain ⟨u, -, hu⟩ := Finset.exists_max_image Finset.univ y
    ⟨⟨0, hnpos⟩, Finset.mem_univ _⟩
  have hmaxu : ∀ i, y i ≤ y u := fun i => hu i (Finset.mem_univ i)
  have hupos : 0 < y u := by
    by_contra hc
    push_neg at hc
    have h0 : ∀ i, y i = 0 := fun i => le_antisymm ((hmaxu i).trans hc) (hy0 i)
    have : y ⬝ᵥ y = 0 := by simp [dotProduct, h0]
    rw [hyy] at this
    exact one_ne_zero this
  have hdeg := wkx31_deg G y _ hev u hupos hmaxu
  have hdegW : Fintype.card W ≤ G.degree u := by
    have hnR : ((N0 + 2 * Fintype.card W + 2 : ℕ) : ℝ) ≤ n := by exact_mod_cast hn
    push_cast at hnR
    have : (Fintype.card W : ℝ) ≤ G.degree u := by linarith
    exact_mod_cast this
  by_contra hcon
  obtain ⟨w, hw⟩ : ∃ w, ¬ G.Reachable u w := by
    by_contra h
    push_neg at h
    exact hcon ((SimpleGraph.connected_iff G).2
      ⟨fun a b => (h a).symm.trans (h b), ⟨u⟩⟩)
  have huw : u ≠ w := fun e => hw (e ▸ SimpleGraph.Reachable.refl u)
  have hGuw : ¬ G.Adj u w := fun h => hw h.reachable
  let H : SimpleGraph (Fin n) :=
    { Adj := fun i j => (G.Adj i j ∧ i ≠ w ∧ j ≠ w) ∨ (i = w ∧ j = u) ∨ (i = u ∧ j = w)
      symm := ⟨fun i j h => by
        rcases h with ⟨h1, h2, h3⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inl ⟨h1.symm, h3, h2⟩
        · exact Or.inr (Or.inr ⟨h2, h1⟩)
        · exact Or.inr (Or.inl ⟨h2, h1⟩)⟩
      loopless := ⟨fun i h => by
        rcases h with ⟨h1, -, -⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact G.loopless.irrefl i h1
        · exact huw (h2.symm.trans h1)
        · exact huw (h1.symm.trans h2)⟩ }
  have hH : ∀ i j, H.Adj i j ↔
      (G.Adj i j ∧ i ≠ w ∧ j ≠ w) ∨ (i = w ∧ j = u) ∨ (i = u ∧ j = w) := fun i j => Iff.rfl
  have hHfree' : F.Free H := wkx31_free F G H hfree u w huw hGuw hdegW hH
  have hev' := wkx31_restrict G y _ hev u
  have hgain := wkx31_gain G H (fun i => if G.Reachable u i then y i else 0) _ hev' u w huw
    (by simp only [if_pos (SimpleGraph.Reachable.refl u)]; exact hupos)
    (by simp only [if_neg hw]) hH
  exact absurd (hmax H hHfree') (not_le.2 hgain)
