-- Prove2me | solution 1 for WangKangXue.SpectralTuran.theorem_1_2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-10T05:27:35.972069+00:00
-- url     : https://prove2.me/submissions/91924ec4-79da-4c4f-946d-80a1560697c0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WangKangXue_SpectralTuran_specRad
import Definitions.Def_WangKangXue_SpectralTuran_IsSpectralExtremal
import Definitions.Def_WangKangXue_SpectralTuran_TuranPlusEdges
import Definitions.Def_WangKangXue_SpectralTuran_IsMaxCut
import Theorems.Thm_WangKangXue_SpectralTuran_lemma_3_1
import Theorems.Thm_WangKangXue_SpectralTuran_lemma_3_7
import Theorems.Thm_WangKangXue_SpectralTuran_lemma_3_8
import Theorems.Thm_WangKangXue_SpectralTuran_lemma_3_10

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



section WKXGlue

open WangKangXue.SpectralTuran

open Matrix in
theorem wkx_quad_iso {V V' : Type*} [Fintype V] [DecidableEq V] [Fintype V'] [DecidableEq V']
    {G : SimpleGraph V} {G' : SimpleGraph V'} [DecidableRel G.Adj] [DecidableRel G'.Adj]
    (e : G ≃g G') (v : V → ℝ) :
    (v ∘ e.symm) ⬝ᵥ (G'.adjMatrix ℝ *ᵥ (v ∘ e.symm)) = v ⬝ᵥ (G.adjMatrix ℝ *ᵥ v) := by
  rw [wk9_quad, wk9_quad]
  symm
  refine Fintype.sum_equiv e.toEquiv _ _ (fun i => ?_)
  refine Fintype.sum_equiv e.toEquiv _ _ (fun j => ?_)
  have h : G'.Adj (e i) (e j) ↔ G.Adj i j := e.map_adj_iff
  by_cases hij : G.Adj i j
  · simp [Function.comp, hij, h.2 hij]
  · simp [hij, mt h.1 hij]

open Matrix in
theorem wkx_dot_iso {V V' : Type*} [Fintype V] [Fintype V'] (e : V ≃ V') (v : V → ℝ) :
    (v ∘ e.symm) ⬝ᵥ (v ∘ e.symm) = v ⬝ᵥ v := by
  simp only [dotProduct]
  symm
  exact Fintype.sum_equiv e _ _ (fun i => by simp)

open Matrix in
theorem wkx_specRad_le_of_iso {V V' : Type*} [Fintype V] [DecidableEq V] [Fintype V']
    [DecidableEq V'] {G : SimpleGraph V} {G' : SimpleGraph V'} (e : G ≃g G') :
    specRad G ≤ specRad G' := by
  classical
  unfold specRad
  by_cases h : 0 < Fintype.card V
  · have h' : 0 < Fintype.card V' := by rw [← e.card_eq]; exact h
    rw [dif_pos h, dif_pos h']
    obtain ⟨v, hvv, hv⟩ := wk9_exists (G.isHermitian_adjMatrix ℝ) h
    have hle := wk9_le (G'.isHermitian_adjMatrix ℝ) h' (v ∘ e.symm)
    have h2 : (v ∘ e.symm) ⬝ᵥ (v ∘ e.symm) = 1 := by
      rw [show (v ∘ e.symm) = v ∘ e.toEquiv.symm from rfl, wkx_dot_iso, hvv]
    rw [wkx_quad_iso e v, h2, hv, dotProduct_smul, smul_eq_mul, hvv] at hle
    simpa using hle
  · have h' : ¬ 0 < Fintype.card V' := by rw [← e.card_eq]; exact h
    rw [dif_neg h, dif_neg h']

theorem wkx_specRad_eq_of_iso {V V' : Type*} [Fintype V] [DecidableEq V] [Fintype V']
    [DecidableEq V'] {G : SimpleGraph V} {G' : SimpleGraph V'} (e : G ≃g G') :
    specRad G = specRad G' :=
  le_antisymm (wkx_specRad_le_of_iso e) (wkx_specRad_le_of_iso e.symm)

theorem wkx_exists_maxCut {n r : ℕ} (hr : 0 < r) (G : SimpleGraph (Fin n)) :
    ∃ P : Fin n → Fin r, IsMaxCut G P := by
  obtain ⟨P, -, hP⟩ := Finset.exists_max_image Finset.univ
    (fun P : Fin n → Fin r => crossEdges G P) ⟨fun _ => ⟨0, hr⟩, Finset.mem_univ _⟩
  exact ⟨P, fun P' => hP P' (Finset.mem_univ _)⟩

theorem wkx_sum_card_part {n r : ℕ} (P : Fin n → Fin r) : ∑ i, (part P i).card = n := by
  classical
  have := Finset.card_eq_sum_card_fiberwise (s := (Finset.univ : Finset (Fin n)))
    (t := (Finset.univ : Finset (Fin r))) (f := P) (fun _ _ => Finset.mem_univ _)
  rw [Finset.card_univ, Fintype.card_fin] at this
  refine Eq.trans (Finset.sum_congr rfl (fun i _ => ?_)) this.symm
  unfold part
  congr

theorem wkx_part_nonempty {n r : ℕ} (hn : r ≤ n) (P : Fin n → Fin r)
    (hb : ∀ i j : Fin r, |((part P i).card : ℤ) - ((part P j).card : ℤ)| ≤ 1) (i : Fin r) :
    (part P i).Nonempty := by
  by_contra h
  rw [Finset.not_nonempty_iff_eq_empty] at h
  have hle : ∀ j, (part P j).card ≤ 1 := by
    intro j
    have := hb j i
    rw [h, Finset.card_empty, Nat.cast_zero, sub_zero, abs_le] at this
    omega
  have hlt : ∑ j, (part P j).card < ∑ _j : Fin r, 1 :=
    Finset.sum_lt_sum (fun j _ => hle j) ⟨i, Finset.mem_univ _, by rw [h]; simp⟩
  rw [wkx_sum_card_part] at hlt
  simp at hlt
  omega

theorem wkx_mem_part {n r : ℕ} (P : Fin n → Fin r) (i : Fin r) (v : Fin n) :
    v ∈ part P i ↔ P v = i := by
  unfold part; simp

theorem wkx_iso_turan_of_balanced {n r : ℕ} (hn : r ≤ n) (P : Fin n → Fin r)
    (hb : ∀ i j : Fin r, |((part P i).card : ℤ) - ((part P j).card : ℤ)| ≤ 1) :
    Nonempty (completePartite P ≃g SimpleGraph.turanGraph n r) := by
  classical
  let s : Setoid (Fin n) := Setoid.ker P
  have hsr : ∀ a b, s a b ↔ P a = P b := fun a b => Iff.rfl
  let fp : Finpartition (Finset.univ : Finset (Fin n)) := Finpartition.ofSetoid s
  have hpart : ∀ a, fp.part a = part P (P a) := by
    intro a; ext b
    rw [Finpartition.mem_part_ofSetoid_iff_rel, hsr, wkx_mem_part, eq_comm]
  have hparts : fp.parts = Finset.univ.image (part P) := by
    ext S
    constructor
    · intro hS
      obtain ⟨a, ha⟩ := fp.nonempty_of_mem_parts hS
      rw [Finset.mem_image]
      refine ⟨P a, Finset.mem_univ _, ?_⟩
      rw [← hpart, fp.part_eq_of_mem hS ha]
    · intro hS
      rw [Finset.mem_image] at hS
      obtain ⟨i, -, rfl⟩ := hS
      obtain ⟨a, ha⟩ := wkx_part_nonempty hn P hb i
      have hPa : P a = i := (wkx_mem_part P i a).1 ha
      rw [← hPa, ← hpart]
      exact fp.part_mem.2 (Finset.mem_univ a)
  have hinj : Function.Injective (part P) := by
    intro i j hij
    obtain ⟨a, ha⟩ := wkx_part_nonempty hn P hb i
    have hj : a ∈ part P j := hij ▸ ha
    rw [wkx_mem_part] at ha hj
    exact ha.symm.trans hj
  have hcard : fp.parts.card = r := by
    rw [hparts, Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  have heq : fp.IsEquipartition := by
    intro S T hS hT
    rw [Finset.mem_coe, hparts, Finset.mem_image] at hS hT
    obtain ⟨i, -, rfl⟩ := hS
    obtain ⟨j, -, rfl⟩ := hT
    have := hb i j
    rw [abs_le] at this
    omega
  obtain ⟨zm, zp⟩ := heq.exists_partPreservingEquiv
  have hcu : (Finset.univ : Finset (Fin n)).card = n := by
    rw [Finset.card_univ, Fintype.card_fin]
  let g : Fin n ≃ Fin n :=
    (Equiv.subtypeUnivEquiv Finset.mem_univ).symm.trans (zm.trans (finCongr hcu))
  refine ⟨⟨g, ?_⟩⟩
  intro a b
  rw [SimpleGraph.turanGraph_adj]
  change (g a : ℕ) % r ≠ (g b : ℕ) % r ↔ P a ≠ P b
  have := zp ⟨a, Finset.mem_univ a⟩ ⟨b, Finset.mem_univ b⟩
  rw [hpart, hpart, hcard] at this
  have hPP : part P (P a) = part P (P b) ↔ P a = P b := hinj.eq_iff
  rw [hPP] at this
  rw [ne_eq, ne_eq, not_iff_not, this]
  exact Iff.rfl

open Classical in
theorem wkx_card_partite_eq_turan {n r : ℕ} (hn : r ≤ n) (P : Fin n → Fin r)
    (hb : ∀ i j : Fin r, |((part P i).card : ℤ) - ((part P j).card : ℤ)| ≤ 1) :
    (completePartite P).edgeFinset.card = (SimpleGraph.turanGraph n r).edgeFinset.card := by
  obtain ⟨e⟩ := wkx_iso_turan_of_balanced hn P hb
  exact e.card_edgeFinset_eq

theorem wkx_specRad_partite_eq_turan {n r : ℕ} (hn : r ≤ n) (P : Fin n → Fin r)
    (hb : ∀ i j : Fin r, |((part P i).card : ℤ) - ((part P j).card : ℤ)| ≤ 1) :
    specRad (completePartite P) = specRad (SimpleGraph.turanGraph n r) := by
  obtain ⟨e⟩ := wkx_iso_turan_of_balanced hn P hb
  exact wkx_specRad_eq_of_iso e

open Classical in
theorem wkx_exists_extremal {W : Type*} (F : SimpleGraph W) {n : ℕ} (G : SimpleGraph (Fin n))
    (hG : F.Free G) :
    ∃ H : SimpleGraph (Fin n), F.Free H ∧ H.edgeFinset.card = SimpleGraph.extremalNumber n F := by
  obtain ⟨H, inst, hH⟩ := (SimpleGraph.exists_isExtremal_iff_exists F.Free).2 ⟨G, hG⟩
  rw [SimpleGraph.isExtremal_free_iff, Fintype.card_fin] at hH
  exact ⟨H, hH.1, by convert hH.2⟩

/-! ### N1 (pure Rayleigh comparison): if `x` is an eigenvector of `A(G)` for `λ(G)` with
`1 - δ ≤ x ≤ 1`, then for any graph `K` on the same vertices
`λ(G) ≤ λ(K) + 2(e(G\K) - e(K\G))/n + 8δ(e(G\K) + e(K\G))/n`. -/

open Classical in
theorem wkx_quad_count {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) :
    (∑ u, ∑ v, (if H.Adj u v then (1 : ℝ) else 0)) = 2 * (H.edgeFinset.card : ℝ) := by
  have h := H.sum_degrees_eq_twice_card_edges
  have hd : ∀ u, (∑ v, (if H.Adj u v then (1 : ℝ) else 0)) = (H.degree u : ℝ) := by
    intro u
    rw [Finset.sum_boole, ← H.card_neighborFinset_eq_degree]
    congr 2
    ext v
    simp
  simp_rw [hd]
  have h' : ((∑ u, H.degree u : ℕ) : ℝ) = ((2 * H.edgeFinset.card : ℕ) : ℝ) := by
    rw [h]
  push_cast at h'
  exact h'

open Classical in
theorem wkx_quad_bounds {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (x : V → ℝ) (lo : ℝ) (hlo0 : 0 ≤ lo) (hlo : ∀ u, lo ≤ x u) (hhi : ∀ u, x u ≤ 1) :
    lo ^ 2 * (2 * (H.edgeFinset.card : ℝ)) ≤
        ∑ u, ∑ v, (if H.Adj u v then x u * x v else 0) ∧
      ∑ u, ∑ v, (if H.Adj u v then x u * x v else 0) ≤ 2 * (H.edgeFinset.card : ℝ) := by
  rw [← wkx_quad_count H]
  constructor
  · rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun u _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun v _ => ?_)
    split_ifs
    · have h1 := hlo u
      have h2 := hlo v
      nlinarith [mul_le_mul h1 h2 hlo0 (le_trans hlo0 h1)]
    · simp
  · refine Finset.sum_le_sum (fun u _ => Finset.sum_le_sum (fun v _ => ?_))
    split_ifs
    · have h1 := hhi u
      have h2 := hhi v
      have h3 := le_trans hlo0 (hlo u)
      have h4 := le_trans hlo0 (hlo v)
      nlinarith [mul_le_mul h1 h2 h4 zero_le_one]
    · exact le_rfl

open Classical in
theorem wkx_quad_split {V : Type*} [Fintype V] [DecidableEq V] (G K : SimpleGraph V)
    (x : V → ℝ) :
    ∑ u, ∑ v, (if G.Adj u v then x u * x v else 0) =
      ∑ u, ∑ v, (if K.Adj u v then x u * x v else 0) +
        ∑ u, ∑ v, (if (G \ K).Adj u v then x u * x v else 0) -
        ∑ u, ∑ v, (if (K \ G).Adj u v then x u * x v else 0) := by
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun u _ => ?_)
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  simp only [SimpleGraph.sdiff_adj]
  by_cases hG : G.Adj u v <;> by_cases hK : K.Adj u v <;> simp [hG, hK]

open Classical Matrix in
theorem wkx_N1 {V : Type*} [Fintype V] [DecidableEq V] (G K : SimpleGraph V) (x : V → ℝ)
    (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 4)
    (hx : (G.adjMatrix ℝ).mulVec x = specRad G • x)
    (hlo : ∀ u, 1 - δ ≤ x u) (hhi : ∀ u, x u ≤ 1) (hn : 0 < Fintype.card V) :
    specRad G ≤ specRad K +
      2 * (((G \ K).edgeFinset.card : ℝ) - ((K \ G).edgeFinset.card : ℝ)) / Fintype.card V +
      8 * δ * (((G \ K).edgeFinset.card : ℝ) + ((K \ G).edgeFinset.card : ℝ)) /
        Fintype.card V := by
  have hsK : specRad K = (K.isHermitian_adjMatrix ℝ).eigenvalues₀ ⟨0, hn⟩ := by
    unfold specRad; rw [dif_pos hn]
  have hKle := wk9_le (K.isHermitian_adjMatrix ℝ) hn x
  rw [← hsK] at hKle
  have hGeq : x ⬝ᵥ (G.adjMatrix ℝ *ᵥ x) = specRad G * (x ⬝ᵥ x) := by
    rw [hx, dotProduct_smul, smul_eq_mul]
  rw [wk9_quad, wkx_quad_split G K x] at hGeq
  rw [wk9_quad] at hKle
  set ein : ℝ := ((G \ K).edgeFinset.card : ℝ) with hein
  set eout : ℝ := ((K \ G).edgeFinset.card : ℝ) with heout
  set nn : ℝ := (Fintype.card V : ℝ) with hnn
  have hlo0 : 0 ≤ 1 - δ := by linarith
  have hin := (wkx_quad_bounds (G \ K) x (1 - δ) hlo0 hlo hhi).2
  have hout := (wkx_quad_bounds (K \ G) x (1 - δ) hlo0 hlo hhi).1
  replace hin : (∑ u, ∑ v, if (G \ K).Adj u v then x u * x v else 0) ≤ 2 * ein := by
    rw [hein]; convert hin
  replace hout : (1 - δ) ^ 2 * (2 * eout) ≤
      ∑ u, ∑ v, if (K \ G).Adj u v then x u * x v else 0 := by
    rw [heout]; convert hout
  set S : ℝ := x ⬝ᵥ x with hS
  have hSlo : nn * (1 - δ) ^ 2 ≤ S := by
    rw [hS, hnn, dotProduct]
    have : ∑ _u : V, (1 - δ) ^ 2 ≤ ∑ u, x u * x u :=
      Finset.sum_le_sum (fun u _ => by nlinarith [hlo u])
    simpa [mul_comm] using this
  have hShi : S ≤ nn := by
    rw [hS, hnn, dotProduct]
    have : ∑ u, x u * x u ≤ ∑ _u : V, (1 : ℝ) :=
      Finset.sum_le_sum (fun u _ => by nlinarith [hlo u, hhi u])
    simpa using this
  have hnpos : 0 < nn := by rw [hnn]; exact_mod_cast hn
  have hd2 : 0 < (1 - δ) ^ 2 := by nlinarith
  have hSpos : 0 < S := lt_of_lt_of_le (mul_pos hnpos hd2) hSlo
  have hein0 : 0 ≤ ein := by rw [hein]; positivity
  have heout0 : 0 ≤ eout := by rw [heout]; positivity
  -- λ(G) S ≤ λ(K) S + 2 ein - 2 (1-δ)^2 eout
  have hmain : specRad G * S ≤ specRad K * S + 2 * ein - (1 - δ) ^ 2 * (2 * eout) := by
    linarith
  -- 2 ein ≤ S (1 + 4δ) * 2 ein / n  and  (1-δ)^2 2 eout ≥ S (1 - 2δ) 2 eout / n
  have hfac : 1 ≤ (1 - δ) ^ 2 * (1 + 4 * δ) := by
    have hq : 0 ≤ 2 - 7 * δ + 4 * δ ^ 2 := by nlinarith
    have := mul_nonneg hδ0 hq
    nlinarith
  have h1 : 2 * ein * nn ≤ S * ((1 + 4 * δ) * (2 * ein)) := by
    have : nn ≤ S * (1 + 4 * δ) := by nlinarith
    nlinarith
  have h2 : S * ((1 - 2 * δ) * (2 * eout)) ≤ (1 - δ) ^ 2 * (2 * eout) * nn := by
    have h12 : 0 ≤ 1 - 2 * δ := by linarith
    have : (1 - 2 * δ) ≤ (1 - δ) ^ 2 := by nlinarith
    have hA : S * ((1 - 2 * δ) * (2 * eout)) ≤ nn * ((1 - 2 * δ) * (2 * eout)) :=
      mul_le_mul_of_nonneg_right hShi (by positivity)
    have hB : nn * ((1 - 2 * δ) * (2 * eout)) ≤ nn * ((1 - δ) ^ 2 * (2 * eout)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right this (by positivity)) hnpos.le
    nlinarith
  -- conclude: multiply the goal by S * n
  set X : ℝ := specRad K + 2 * (ein - eout) / nn + 8 * δ * (ein + eout) / nn with hX
  have hgoal : specRad G * S * nn ≤ X * S * nn := by
    have e1 : X * S * nn =
        specRad K * S * nn + S * (2 * (ein - eout) + 8 * δ * (ein + eout)) := by
      have hn0 : nn ≠ 0 := hnpos.ne'
      rw [hX]
      field_simp
      ring
    rw [e1]
    have hm := mul_le_mul_of_nonneg_right hmain hnpos.le
    have h3 : 0 ≤ S * (4 * δ * eout) := by positivity
    linarith
  have hSn : 0 < S * nn := mul_pos hSpos hnpos
  have e2 : specRad G * S * nn = specRad G * (S * nn) := by ring
  have e3 : X * S * nn = X * (S * nn) := by ring
  rw [e2, e3] at hgoal
  exact le_of_mul_le_mul_right hgoal hSn

/-! ### N2 (Turán graph plus `a` edges): `λ(H) ≥ λ(T_{n,r}) + 2a/n - 4a/n²`.
The top eigenvector of `T_{n,r}` is constant on parts, `(λ + s_u) v_u = Σ v`, and the part sizes
`s_u` differ by at most one, so all entries agree up to a factor `1 - 1/n`. -/

open Classical in
theorem wkx_quad_lower {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (x : V → ℝ) (lo : ℝ) (hlo0 : 0 ≤ lo) (hlo : ∀ u, lo ≤ x u) :
    lo ^ 2 * (2 * (H.edgeFinset.card : ℝ)) ≤
        ∑ u, ∑ v, (if H.Adj u v then x u * x v else 0) := by
  rw [← wkx_quad_count H, Finset.mul_sum]
  refine Finset.sum_le_sum (fun u _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum (fun v _ => ?_)
  split_ifs
  · have h1 := hlo u
    have h2 := hlo v
    nlinarith [mul_le_mul h1 h2 hlo0 (le_trans hlo0 h1)]
  · simp

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
theorem wkx_turan_perron_aux {n r : ℕ} (hr : 2 ≤ r) (hn : 2 ≤ n) (T : SimpleGraph (Fin n))
    (hTadj : ∀ u w, T.Adj u w ↔ (u : ℕ) % r ≠ (w : ℕ) % r) (v : Fin n → ℝ)
    (hvv : v ⬝ᵥ v = 1) (hv : T.adjMatrix ℝ *ᵥ v = specRad T • v)
    (hS : 0 ≤ ∑ u, v u) :
    (∀ u, 0 < v u) ∧ ∀ u w, (1 - 1 / (n : ℝ)) * v w ≤ v u := by
  set μ := specRad T with hμ
  set S := ∑ u, v u with hSdef
  have hn0 : 0 < Fintype.card (Fin n) := by rw [Fintype.card_fin]; omega
  have hr0 : 0 < r := by omega
  -- μ > 0
  have hμpos : 0 < μ := by
    have hsT : μ = (T.isHermitian_adjMatrix ℝ).eigenvalues₀ ⟨0, hn0⟩ := by
      rw [hμ]; unfold specRad; rw [dif_pos hn0]
    let o : Fin n → ℝ := fun _ => 1
    have hle := wk9_le (T.isHermitian_adjMatrix ℝ) hn0 o
    rw [← hsT, wk9_quad] at hle
    let i0 : Fin n := ⟨0, by omega⟩
    let i1 : Fin n := ⟨1, by omega⟩
    have h01 : T.Adj i0 i1 := by
      rw [hTadj]
      show 0 % r ≠ 1 % r
      rw [Nat.zero_mod, Nat.mod_eq_of_lt (by omega : 1 < r)]
      omega
    have hnn : ∀ i j, 0 ≤ (if T.Adj i j then o i * o j else 0) := by
      intro i j; split_ifs <;> simp [o]
    have hpos : (1 : ℝ) ≤ ∑ i, ∑ j, (if T.Adj i j then o i * o j else 0) := by
      calc (1 : ℝ) = (if T.Adj i0 i1 then o i0 * o i1 else 0) := by
            rw [if_pos h01]; simp [o]
        _ ≤ ∑ j, (if T.Adj i0 j then o i0 * o j else 0) :=
          Finset.single_le_sum (f := fun j => if T.Adj i0 j then o i0 * o j else 0)
            (fun j _ => hnn i0 j) (Finset.mem_univ i1)
        _ ≤ ∑ i, ∑ j, (if T.Adj i j then o i * o j else 0) :=
          Finset.single_le_sum (f := fun i => ∑ j, (if T.Adj i j then o i * o j else 0))
            (fun i _ => Finset.sum_nonneg (fun j _ => hnn i j)) (Finset.mem_univ i0)
    have hdot : o ⬝ᵥ o = n := by
      simp [dotProduct, o]
    rw [hdot] at hle
    have : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    nlinarith
  -- row equation
  have hrow : ∀ u, μ * v u = ∑ w, (if T.Adj u w then v w else 0) := by
    intro u
    have := congrFun hv u
    rw [wk9_row, Pi.smul_apply, smul_eq_mul] at this
    exact this.symm
  -- constant on classes
  have hcls : ∀ u w, ¬ T.Adj u w → v w = v u := by
    intro u w huw
    have hres : (u : ℕ) % r = (w : ℕ) % r := by
      by_contra h; exact huw ((hTadj u w).2 h)
    have hsame : ∀ y, T.Adj u y ↔ T.Adj w y := by
      intro y
      rw [hTadj, hTadj, hres]
    have h1 := hrow u
    have h2 := hrow w
    have : ∑ y, (if T.Adj u y then v y else 0) = ∑ y, (if T.Adj w y then v y else 0) :=
      Finset.sum_congr rfl (fun y _ => by
        by_cases hy : T.Adj u y
        · rw [if_pos hy, if_pos ((hsame y).1 hy)]
        · rw [if_neg hy, if_neg (fun h => hy ((hsame y).2 h))])
    have hm : μ * v u = μ * v w := by rw [h1, h2, this]
    exact (mul_left_cancel₀ hμpos.ne' hm).symm
  -- (μ + s_u) v_u = S
  set s : Fin n → ℝ := fun u =>
    ((Finset.univ.filter (fun y => ¬ T.Adj u y)).card : ℝ) with hs
  have heq : ∀ u, (μ + s u) * v u = S := by
    intro u
    have hsplit : S = ∑ w, (if T.Adj u w then v w else 0) +
        ∑ w, (if ¬ T.Adj u w then v w else 0) := by
      rw [hSdef, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun w _ => ?_)
      by_cases h : T.Adj u w <;> simp [h]
    have hna : ∑ w, (if ¬ T.Adj u w then v w else 0) = s u * v u := by
      rw [hs]
      simp only
      rw [← Finset.sum_filter, Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl (fun w hw => ?_)
      rw [Finset.mem_filter] at hw
      rw [hcls u w hw.2]
      simp
    rw [hsplit, hna, ← hrow u]
    ring
  have hs0 : ∀ u, 0 ≤ s u := fun u => by rw [hs]; positivity
  have hDpos : ∀ u, 0 < μ + s u := fun u => by linarith [hs0 u]
  -- S > 0
  have hSpos : 0 < S := by
    rcases lt_or_eq_of_le hS with h | h
    · exact h
    · exfalso
      have hz : ∀ u, v u = 0 := by
        intro u
        have := heq u
        rw [← h] at this
        rcases mul_eq_zero.mp this with h1 | h1
        · exact absurd h1 (hDpos u).ne'
        · exact h1
      have : v ⬝ᵥ v = 0 := by simp [dotProduct, hz]
      rw [hvv] at this
      exact one_ne_zero this
  have hvpos : ∀ u, 0 < v u := by
    intro u
    have := heq u
    by_contra hc
    push Not at hc
    nlinarith [hDpos u]
  refine ⟨hvpos, fun u w => ?_⟩
  have hbal : ∀ z y, s z ≤ s y + 1 := fun z y => wkx_class_balanced_of hr0 T hTadj z y
  have hDp : 0 < μ + s w + 1 := by linarith [hDpos w]
  -- D := μ + s w + 1 ≥ n
  have hD : (n : ℝ) ≤ μ + s w + 1 := by
    have hlow : ∀ z, S / (μ + s w + 1) ≤ v z := by
      intro z
      rw [div_le_iff₀ hDp]
      have := heq z
      have hb := hbal z w
      nlinarith [hvpos z]
    have hsum : ∑ _z : Fin n, S / (μ + s w + 1) ≤ S :=
      Finset.sum_le_sum (fun z _ => hlow z)
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
    rw [mul_div_assoc', div_le_iff₀ hDp] at hsum
    nlinarith
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have huw : v w * (μ + s w) ≤ v u * (μ + s w + 1) := by
    have h1 := heq u
    have h2 := heq w
    have hb := hbal u w
    nlinarith [hvpos u]
  have hk : v w * (1 - 1 / (n : ℝ)) ≤ v w * (1 - 1 / (μ + s w + 1)) := by
    have : 1 / (μ + s w + 1) ≤ 1 / (n : ℝ) := one_div_le_one_div_of_le hnpos hD
    nlinarith [hvpos w]
  have hk2 : v w * (1 - 1 / (μ + s w + 1)) ≤ v u := by
    have e : v w * (1 - 1 / (μ + s w + 1)) = v w * (μ + s w) / (μ + s w + 1) := by
      field_simp
      ring
    rw [e, div_le_iff₀ hDp]
    linarith
  linarith

open Classical Matrix in
theorem wkx_turan_perron {n r : ℕ} (hr : 2 ≤ r) (hn : 2 ≤ n) (T : SimpleGraph (Fin n))
    (hTadj : ∀ u w, T.Adj u w ↔ (u : ℕ) % r ≠ (w : ℕ) % r) :
    ∃ v : Fin n → ℝ, v ⬝ᵥ v = 1 ∧ T.adjMatrix ℝ *ᵥ v = specRad T • v ∧
      (∀ u, 0 < v u) ∧ ∀ u w, (1 - 1 / (n : ℝ)) * v w ≤ v u := by
  have hn0 : 0 < Fintype.card (Fin n) := by rw [Fintype.card_fin]; omega
  obtain ⟨v, hvv, hv⟩ := wk9_exists (T.isHermitian_adjMatrix ℝ) hn0
  have hsT : specRad T = (T.isHermitian_adjMatrix ℝ).eigenvalues₀ ⟨0, hn0⟩ := by
    unfold specRad; rw [dif_pos hn0]
  rw [← hsT] at hv
  by_cases hS : 0 ≤ ∑ u, v u
  · exact ⟨v, hvv, hv, wkx_turan_perron_aux hr hn T hTadj v hvv hv hS⟩
  · have hvv' : (-v) ⬝ᵥ (-v) = 1 := by simpa using hvv
    have hv' : T.adjMatrix ℝ *ᵥ (-v) = specRad T • (-v) := by
      rw [mulVec_neg, hv, smul_neg]
    refine ⟨-v, hvv', hv', ?_⟩
    apply wkx_turan_perron_aux hr hn T hTadj (-v) hvv' hv'
    push Not at hS
    simp only [Pi.neg_apply, Finset.sum_neg_distrib]
    linarith

open Classical Matrix in
theorem wkx_N2_core {n r : ℕ} (hr : 2 ≤ r) (hn : 2 ≤ n) (T H : SimpleGraph (Fin n))
    (hTadj : ∀ u w, T.Adj u w ↔ (u : ℕ) % r ≠ (w : ℕ) % r) (hTH : T ≤ H) (k : ℕ)
    (hk : (H \ T).edgeFinset.card = k) :
    specRad T + 2 * (k : ℝ) / n - 4 * (k : ℝ) / (n : ℝ) ^ 2 ≤ specRad H := by
  have hn0 : 0 < Fintype.card (Fin n) := by rw [Fintype.card_fin]; omega
  obtain ⟨v, hvv, hv, hvpos, hratio⟩ := wkx_turan_perron hr hn T hTadj
  have hsH : specRad H = (H.isHermitian_adjMatrix ℝ).eigenvalues₀ ⟨0, hn0⟩ := by
    unfold specRad; rw [dif_pos hn0]
  have hHle := wk9_le (H.isHermitian_adjMatrix ℝ) hn0 v
  rw [← hsH, hvv, mul_one, wk9_quad, wkx_quad_split H T v] at hHle
  have hTq : ∑ u, ∑ w, (if T.Adj u w then v u * v w else 0) = specRad T := by
    rw [← wk9_quad, hv, dotProduct_smul, hvv, smul_eq_mul, mul_one]
  have hTH0 : ∑ u, ∑ w, (if (T \ H).Adj u w then v u * v w else 0) = 0 := by
    refine Finset.sum_eq_zero (fun u _ => Finset.sum_eq_zero (fun w _ => ?_))
    rw [if_neg]
    rw [SimpleGraph.sdiff_adj]
    rintro ⟨h1, h2⟩
    exact h2 (hTH h1)
  rw [hTq, hTH0, sub_zero] at hHle
  -- min and max entries
  obtain ⟨um, -, hum⟩ := Finset.exists_min_image Finset.univ v
    ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  obtain ⟨uM, -, huM⟩ := Finset.exists_max_image Finset.univ v
    ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  have hm0 : 0 ≤ v um := (hvpos um).le
  have hQ := wkx_quad_lower (H \ T) v (v um) hm0 (fun u => hum u (Finset.mem_univ _))
  set e : ℝ := (k : ℝ) with he
  replace hQ : v um ^ 2 * (2 * e) ≤
      ∑ u, ∑ w, (if (H \ T).Adj u w then v u * v w else 0) := by
    rw [he, ← hk]; convert hQ
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hM2 : 1 ≤ (n : ℝ) * v uM ^ 2 := by
    rw [← hvv, dotProduct]
    have : ∑ u, v u * v u ≤ ∑ _u : Fin n, v uM ^ 2 :=
      Finset.sum_le_sum (fun u _ => by
        have h1 := huM u (Finset.mem_univ _)
        have h2 := (hvpos u).le
        nlinarith)
    simpa using this
  have hmM : (1 - 1 / (n : ℝ)) * v uM ≤ v um := hratio um uM
  have hk1 : 0 ≤ 1 - 1 / (n : ℝ) := by
    rw [sub_nonneg, div_le_one hnpos]; linarith
  have hm2 : (1 - 2 / (n : ℝ)) * v uM ^ 2 ≤ v um ^ 2 := by
    have h1 : ((1 - 1 / (n : ℝ)) * v uM) ^ 2 ≤ v um ^ 2 :=
      pow_le_pow_left₀ (mul_nonneg hk1 (hvpos uM).le) hmM 2
    have h2 : (1 - 2 / (n : ℝ)) ≤ (1 - 1 / (n : ℝ)) ^ 2 := by
      have : 0 ≤ (1 / (n : ℝ)) ^ 2 := sq_nonneg _
      have e2 : (1 - 1 / (n : ℝ)) ^ 2 = 1 - 2 / (n : ℝ) + (1 / (n : ℝ)) ^ 2 := by ring
      linarith
    have h3 : (1 - 2 / (n : ℝ)) * v uM ^ 2 ≤ (1 - 1 / (n : ℝ)) ^ 2 * v uM ^ 2 :=
      mul_le_mul_of_nonneg_right h2 (sq_nonneg _)
    calc (1 - 2 / (n : ℝ)) * v uM ^ 2 ≤ (1 - 1 / (n : ℝ)) ^ 2 * v uM ^ 2 := h3
      _ = ((1 - 1 / (n : ℝ)) * v uM) ^ 2 := by ring
      _ ≤ v um ^ 2 := h1
  have he0 : 0 ≤ e := by rw [he]; positivity
  have hfinal : 2 * e / n - 4 * e / (n : ℝ) ^ 2 ≤ v um ^ 2 * (2 * e) := by
    have hc : 0 ≤ 1 - 2 / (n : ℝ) := by
      rw [sub_nonneg, div_le_one hnpos]; exact hn2
    have hM2' : 1 / (n : ℝ) ≤ v uM ^ 2 := by
      rw [div_le_iff₀ hnpos]; linarith
    have h3 : (1 - 2 / (n : ℝ)) * (1 / n) ≤ v um ^ 2 :=
      le_trans (mul_le_mul_of_nonneg_left hM2' hc) hm2
    have e4 : 2 * e / n - 4 * e / (n : ℝ) ^ 2 = (1 - 2 / (n : ℝ)) * (1 / n) * (2 * e) := by
      field_simp
      ring
    rw [e4]
    exact mul_le_mul_of_nonneg_right h3 (by linarith)
  linarith

open Classical in
/-- N2 in the form used by the parent: `T_{n,r}` contained in `H` with `a` extra edges. -/
theorem wkx_N2 (r a : ℕ) (hr : 2 ≤ r) :
    ∀ n ≥ 2, ∀ H : SimpleGraph (Fin n),
      (SimpleGraph.turanGraph n r).IsContained H →
      H.edgeFinset.card = (SimpleGraph.turanGraph n r).edgeFinset.card + a →
      specRad (SimpleGraph.turanGraph n r) + 2 * (a : ℝ) / n - 4 * (a : ℝ) / (n : ℝ) ^ 2 ≤
        specRad H := by
  intro n hn H hc hcard
  obtain ⟨f⟩ := hc
  have hbij : Function.Bijective f.toHom := (Finite.injective_iff_bijective).1 f.injective
  let e : Fin n ≃ Fin n := Equiv.ofBijective f.toHom hbij
  let H' : SimpleGraph (Fin n) := H.comap f.toHom
  have hiso : H' ≃g H := ⟨e, by intro a b; rfl⟩
  have hTH : SimpleGraph.turanGraph n r ≤ H' := by
    intro u w huw
    exact f.toHom.map_adj huw
  have hspec : specRad H' = specRad H := wkx_specRad_eq_of_iso hiso
  have hcard' : H'.edgeFinset.card = H.edgeFinset.card := hiso.card_edgeFinset_eq
  have hsub : (SimpleGraph.turanGraph n r).edgeFinset ⊆ H'.edgeFinset :=
    SimpleGraph.edgeFinset_subset_edgeFinset.2 hTH
  have hdiff : (H' \ SimpleGraph.turanGraph n r).edgeFinset.card = a := by
    have hs : (H' \ SimpleGraph.turanGraph n r).edgeFinset =
        H'.edgeFinset \ (SimpleGraph.turanGraph n r).edgeFinset := by
      ext x; simp
    rw [hs]
    have h1 := Finset.card_sdiff_add_card_inter H'.edgeFinset
      (SimpleGraph.turanGraph n r).edgeFinset
    rw [Finset.inter_eq_right.2 hsub] at h1
    omega
  have hcore := wkx_N2_core hr hn (SimpleGraph.turanGraph n r) H'
    (fun u w => SimpleGraph.turanGraph_adj) hTH a (by convert hdiff)
  rw [hspec] at hcore
  linarith

/-! ### Glue for the reduction: Perron vector, counting from Lemma 3.7, final assembly. -/

open Classical in
theorem wkx_bookkeeping {n r : ℕ} (G : SimpleGraph (Fin n)) (P : Fin n → Fin r) :
    G.edgeFinset.card + (completePartite P \ G).edgeFinset.card =
      (completePartite P).edgeFinset.card + (G \ completePartite P).edgeFinset.card := by
  have hs1 : (completePartite P \ G).edgeFinset =
      (completePartite P).edgeFinset \ G.edgeFinset := by
    ext e; simp
  have hs2 : (G \ completePartite P).edgeFinset =
      G.edgeFinset \ (completePartite P).edgeFinset := by
    ext e; simp
  rw [hs1, hs2]
  have h1 := Finset.card_sdiff_add_card_inter G.edgeFinset (completePartite P).edgeFinset
  have h2 := Finset.card_sdiff_add_card_inter (completePartite P).edgeFinset G.edgeFinset
  rw [Finset.inter_comm] at h2
  omega

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

open Classical in
theorem wkx_count {n r a : ℕ} (G : SimpleGraph (Fin n)) (P : Fin n → Fin r)
    (h37 : ∀ i : Fin r,
        ((part P i).filter (fun u => 1 ≤ ((G.neighborFinset u) ∩ part P i).card)).card
            ≤ 2 * a ∧
        ∀ u ∈ (part P i).filter (fun u => ((G.neighborFinset u) ∩ part P i).card = 0),
          ∀ w : Fin n, P w ≠ i → G.Adj u w) :
    (G \ completePartite P).edgeFinset.card ≤ (2 * a * r) ^ 2 ∧
      (completePartite P \ G).edgeFinset.card ≤ (2 * a * r) ^ 2 := by
  set B : Finset (Fin n) := (Finset.univ : Finset (Fin r)).biUnion
    (fun i => (part P i).filter (fun u => 1 ≤ ((G.neighborFinset u) ∩ part P i).card)) with hB
  have hBcard : B.card ≤ 2 * a * r := by
    calc B.card ≤ ∑ i, ((part P i).filter
          (fun u => 1 ≤ ((G.neighborFinset u) ∩ part P i).card)).card := Finset.card_biUnion_le
      _ ≤ ∑ _i : Fin r, 2 * a := Finset.sum_le_sum (fun i _ => (h37 i).1)
      _ = 2 * a * r := by simp [mul_comm]
  have hmemB : ∀ u, 1 ≤ ((G.neighborFinset u) ∩ part P (P u)).card → u ∈ B := by
    intro u hu
    rw [hB, Finset.mem_biUnion]
    exact ⟨P u, Finset.mem_univ _, Finset.mem_filter.2 ⟨(wkx_mem_part P _ u).2 rfl, hu⟩⟩
  have hsub : ∀ H : SimpleGraph (Fin n), (∀ u w, H.Adj u w → u ∈ B ∧ w ∈ B) →
      H.edgeFinset.card ≤ (2 * a * r) ^ 2 := by
    intro H hH
    have hss : H.edgeFinset ⊆ (B ×ˢ B).image (fun p : Fin n × Fin n => s(p.1, p.2)) := by
      intro e he
      induction e using Sym2.ind with
      | _ u w =>
        rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
        obtain ⟨hu, hw⟩ := hH u w he
        exact Finset.mem_image.2 ⟨(u, w), Finset.mem_product.2 ⟨hu, hw⟩, rfl⟩
    calc H.edgeFinset.card ≤ ((B ×ˢ B).image (fun p : Fin n × Fin n => s(p.1, p.2))).card := Finset.card_le_card hss
      _ ≤ (B ×ˢ B).card := Finset.card_image_le
      _ = B.card ^ 2 := by rw [Finset.card_product, sq]
      _ ≤ (2 * a * r) ^ 2 := Nat.pow_le_pow_left hBcard 2
  have hin : ∀ u w, G.Adj u w → P u = P w → u ∈ B := by
    intro u w huw hP
    apply hmemB
    apply Finset.card_pos.2
    exact ⟨w, Finset.mem_inter.2 ⟨(G.mem_neighborFinset u w).2 huw,
      (wkx_mem_part P _ w).2 hP.symm⟩⟩
  have hout : ∀ u w, P u ≠ P w → ¬ G.Adj u w → u ∈ B := by
    intro u w hP hnadj
    by_contra hu
    have h0 : ((G.neighborFinset u) ∩ part P (P u)).card = 0 := by
      by_contra hne
      exact hu (hmemB u (by omega))
    exact hnadj ((h37 (P u)).2 u (Finset.mem_filter.2 ⟨(wkx_mem_part P _ u).2 rfl, h0⟩) w
      (fun h => hP h.symm))
  constructor
  · have hh := hsub (G \ completePartite P) (by
      intro u w h
      rw [SimpleGraph.sdiff_adj] at h
      have hP : P u = P w := by
        by_contra hc
        exact h.2 hc
      exact ⟨hin u w h.1 hP, hin w u h.1.symm hP.symm⟩)
    convert hh
  · have hh := hsub (completePartite P \ G) (by
      intro u w h
      rw [SimpleGraph.sdiff_adj] at h
      exact ⟨hout u w h.1 h.2, hout w u (fun e => h.1 e.symm) (fun e => h.2 e.symm)⟩)
    convert hh

open Classical in
/-- Parent assembly: Theorem 1.2 from Lemmas 3.1, 3.7, 3.8 and 3.10 (statements verbatim, as
hypotheses), via the spectral comparisons `wkx_N1`, `wkx_N2`. -/
theorem wkx_glue2 {W : Type*} [Fintype W] (F : SimpleGraph W) (r a : ℕ) (hr : 2 ≤ r)
    (hF : TuranPlusEdges F r a)
    (h31 : ∃ N : ℕ, ∀ n ≥ N, ∀ G : SimpleGraph (Fin n), IsSpectralExtremal F G →
      G.Connected)
    (h37 : ∃ N : ℕ, ∀ n ≥ N, ∀ G : SimpleGraph (Fin n), IsSpectralExtremal F G →
      ∀ P : Fin n → Fin r, IsMaxCut G P → ∀ i : Fin r,
        ((part P i).filter (fun u => 1 ≤ ((G.neighborFinset u) ∩ part P i).card)).card
            ≤ 2 * a ∧
        ∀ u ∈ (part P i).filter (fun u => ((G.neighborFinset u) ∩ part P i).card = 0),
          ∀ w : Fin n, P w ≠ i → G.Adj u w)
    (h38 : 1 ≤ a → ∃ N : ℕ, ∀ n ≥ N, ∀ G : SimpleGraph (Fin n), IsSpectralExtremal F G →
      ∀ x : Fin n → ℝ, (G.adjMatrix ℝ).mulVec x = specRad G • x →
        (∀ i, 0 < x i) → (∀ i, x i ≤ 1) → (∃ z, x z = 1) →
        ∀ u : Fin n, 1 - 20 * (a : ℝ) ^ 2 * (r : ℝ) ^ 2 / n ≤ x u)
    (h310 : ∃ N : ℕ, ∀ n ≥ N, ∀ G : SimpleGraph (Fin n), IsSpectralExtremal F G →
      ∀ P : Fin n → Fin r, IsMaxCut G P →
        ∀ i j : Fin r, |((part P i).card : ℤ) - ((part P j).card : ℤ)| ≤ 1) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ G : SimpleGraph (Fin n), IsSpectralExtremal F G →
      G.edgeFinset.card = SimpleGraph.extremalNumber n F := by
  obtain ⟨N0, hN0⟩ := hF
  obtain ⟨N7, h7⟩ := h37
  obtain ⟨N10, h10⟩ := h310
  have hr0 : 0 < r := by omega
  rcases Nat.eq_zero_or_pos a with ha | ha
  · -- a = 0: Lemma 3.7 forces `G = K_P`, and Lemma 3.10 makes `K_P ≅ T_{n,r}`.
    subst ha
    refine ⟨max (max N0 N7) (max N10 r), ?_⟩
    intro n hn G hG
    have hn0 : N0 ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
    have hn7 : N7 ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
    have hn10 : N10 ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
    have hnr : r ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn
    obtain ⟨P, hP⟩ := wkx_exists_maxCut hr0 G
    have hGK : G = completePartite P := by
      ext u w
      have hu : u ∈ part P (P u) := (wkx_mem_part P _ u).2 rfl
      have h7u := h7 n hn7 G hG P hP (P u)
      have hz : ((G.neighborFinset u) ∩ part P (P u)).card = 0 := by
        by_contra hne
        have hmem : u ∈ (part P (P u)).filter
            (fun u' => 1 ≤ ((G.neighborFinset u') ∩ part P (P u)).card) :=
          Finset.mem_filter.2 ⟨hu, by omega⟩
        have := h7u.1
        rw [Nat.mul_zero, Nat.le_zero, Finset.card_eq_zero] at this
        rw [this] at hmem
        exact absurd hmem (Finset.notMem_empty _)
      constructor
      · intro hadj
        change P u ≠ P w
        intro hPw
        have : w ∈ (G.neighborFinset u) ∩ part P (P u) :=
          Finset.mem_inter.2 ⟨(G.mem_neighborFinset u w).2 hadj,
            (wkx_mem_part P _ w).2 hPw.symm⟩
        rw [Finset.card_eq_zero] at hz
        rw [hz] at this
        exact absurd this (Finset.notMem_empty _)
      · intro hK
        exact h7u.2 u (Finset.mem_filter.2 ⟨hu, hz⟩) w (fun h => hK h.symm)
    subst hGK
    rw [wkx_card_partite_eq_turan hnr P (h10 n hn10 _ hG P hP), (hN0 n hn0).1, Nat.add_zero]
  · -- a ≥ 1: spectral comparison with an extremal graph `H ⊇ T_{n,r}`.
    obtain ⟨N1, h1⟩ := h31
    obtain ⟨N8, h8⟩ := h38 ha
    have hC2 := wkx_N2 r a hr
    set K0 : ℕ := 2 * a + 8 * (20 * a ^ 2 * r ^ 2) * (2 * a * r) ^ 2 + 80 * a ^ 2 * r ^ 2 +
      4 * a + 1 with hK0
    refine ⟨max (max (max N0 N10) (max N1 2)) (max (max N7 N8) (max r K0)), ?_⟩
    intro n hn G hG
    have hn0 : N0 ≤ n := le_trans (le_trans (le_max_left _ _)
      (le_trans (le_max_left _ _) (le_max_left _ _))) hn
    have hn10 : N10 ≤ n := le_trans (le_trans (le_max_right _ _)
      (le_trans (le_max_left _ _) (le_max_left _ _))) hn
    have hn1 : N1 ≤ n := le_trans (le_trans (le_max_left _ _)
      (le_trans (le_max_right _ _) (le_max_left _ _))) hn
    have hn2 : 2 ≤ n := le_trans (le_trans (le_max_right _ _)
      (le_trans (le_max_right _ _) (le_max_left _ _))) hn
    have hn7 : N7 ≤ n := le_trans (le_trans (le_max_left _ _)
      (le_trans (le_max_left _ _) (le_max_right _ _))) hn
    have hn8 : N8 ≤ n := le_trans (le_trans (le_max_right _ _)
      (le_trans (le_max_left _ _) (le_max_right _ _))) hn
    have hnr : r ≤ n := le_trans (le_trans (le_max_left _ _)
      (le_trans (le_max_right _ _) (le_max_right _ _))) hn
    have hnK : K0 ≤ n := le_trans (le_trans (le_max_right _ _)
      (le_trans (le_max_right _ _) (le_max_right _ _))) hn
    obtain ⟨P, hP⟩ := wkx_exists_maxCut hr0 G
    have hb := h10 n hn10 G hG P hP
    -- Perron vector of `G` and Lemma 3.8
    obtain ⟨x, hx, hxpos, hx1, hz⟩ := wkx_perron_connected G (h1 n hn1 G hG)
    have hlo := h8 n hn8 G hG x hx hxpos hx1 hz
    set δ : ℝ := 20 * (a : ℝ) ^ 2 * (r : ℝ) ^ 2 / n with hδ
    have hnpos : (0 : ℝ) < n := by
      have : 0 < n := by omega
      exact_mod_cast this
    have hKr : (K0 : ℝ) ≤ n := by exact_mod_cast hnK
    have hK0r : (K0 : ℝ) = 2 * a + 8 * (20 * a ^ 2 * r ^ 2) * (2 * a * r) ^ 2 +
        80 * a ^ 2 * r ^ 2 + 4 * a + 1 := by
      rw [hK0]; push_cast; ring
    have hcd0 : (0 : ℝ) ≤ 20 * (a : ℝ) ^ 2 * (r : ℝ) ^ 2 := by positivity
    have hE0 : (0 : ℝ) ≤ (2 * (a : ℝ) * r) ^ 2 := by positivity
    have hcdE : (0 : ℝ) ≤ 20 * (a : ℝ) ^ 2 * (r : ℝ) ^ 2 * (2 * (a : ℝ) * r) ^ 2 :=
      mul_nonneg hcd0 hE0
    have hδ0 : 0 ≤ δ := by rw [hδ]; positivity
    have hδ4 : δ ≤ 1 / 4 := by
      rw [hδ, div_le_iff₀ hnpos]
      nlinarith
    have hN1 := wkx_N1 G (completePartite P) x δ hδ0 hδ4 hx hlo hx1
      (by rw [Fintype.card_fin]; omega)
    rw [Fintype.card_fin, wkx_specRad_partite_eq_turan hnr P hb] at hN1
    -- counting from Lemma 3.7
    obtain ⟨hcin, hcout⟩ := wkx_count G P (h7 n hn7 G hG P hP)
    -- an extremal graph `H`
    obtain ⟨H, hHfree, hHcard⟩ := wkx_exists_extremal F G hG.1
    have hHT := (hN0 n hn0).2 H hHfree hHcard
    have hHa : H.edgeFinset.card = (SimpleGraph.turanGraph n r).edgeFinset.card + a := by
      rw [hHcard, (hN0 n hn0).1]
    have hlamH := hC2 n hn2 H hHT hHa
    have hlamG := hG.2 H hHfree
    have hbk := wkx_bookkeeping G P
    rw [wkx_card_partite_eq_turan hnr P hb] at hbk
    have hle : G.edgeFinset.card ≤ SimpleGraph.extremalNumber n F := by
      have := SimpleGraph.card_edgeFinset_le_extremalNumber hG.1
      rw [Fintype.card_fin] at this
      convert this
    -- the integer step: `e(G_in) - e(G_out) ≥ a`
    have hd : (completePartite P \ G).edgeFinset.card + a ≤
        (G \ completePartite P).edgeFinset.card := by
      by_contra hcon
      push Not at hcon
      set ein : ℝ := ((G \ completePartite P).edgeFinset.card : ℝ) with hein
      set eout : ℝ := ((completePartite P \ G).edgeFinset.card : ℝ) with heout
      have hcR : ein + 1 ≤ eout + a := by
        rw [hein, heout]; exact_mod_cast hcon
      have hinR : ein ≤ (2 * (a : ℝ) * r) ^ 2 := by
        rw [hein]; exact_mod_cast hcin
      have houtR : eout ≤ (2 * (a : ℝ) * r) ^ 2 := by
        rw [heout]; exact_mod_cast hcout
      have hein0 : 0 ≤ ein := by rw [hein]; positivity
      have heout0 : 0 ≤ eout := by rw [heout]; positivity
      set X : ℝ := (n : ℝ) with hX
      have key : 2 * (a : ℝ) / X - (4 * a) / X ^ 2 ≤
          2 * (ein - eout) / X + 8 * δ * (ein + eout) / X := by
        linarith
      have hx2 : (0 : ℝ) < X ^ 2 := by positivity
      have e1 : (2 * (a : ℝ) / X - (4 * a) / X ^ 2) * X ^ 2 = 2 * a * X - 4 * a := by
        field_simp
      have e2 : (2 * (ein - eout) / X + 8 * δ * (ein + eout) / X) * X ^ 2 =
          2 * (ein - eout) * X + 8 * (20 * (a : ℝ) ^ 2 * (r : ℝ) ^ 2) * (ein + eout) := by
        rw [hδ]
        field_simp
      have key2 := mul_le_mul_of_nonneg_right key hx2.le
      rw [e1, e2] at key2
      have h3 : 2 * (ein - eout) * X ≤ 2 * ((a : ℝ) - 1) * X :=
        mul_le_mul_of_nonneg_right (by linarith) hnpos.le
      have h4 : 8 * (20 * (a : ℝ) ^ 2 * (r : ℝ) ^ 2) * (ein + eout) ≤
          8 * (20 * (a : ℝ) ^ 2 * (r : ℝ) ^ 2) * (2 * (2 * (a : ℝ) * r) ^ 2) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      have h5 : 8 * (20 * (a : ℝ) ^ 2 * (r : ℝ) ^ 2) * (2 * (2 * (a : ℝ) * r) ^ 2) =
          16 * (20 * (a : ℝ) ^ 2 * (r : ℝ) ^ 2 * (2 * (a : ℝ) * r) ^ 2) := by ring
      have h6 : 2 * ((a : ℝ) - 1) * X = 2 * a * X - 2 * X := by ring
      have h7' : (8 : ℝ) * (20 * a ^ 2 * r ^ 2) * (2 * a * r) ^ 2 =
          8 * (20 * (a : ℝ) ^ 2 * (r : ℝ) ^ 2 * (2 * (a : ℝ) * r) ^ 2) := by ring
      have h8' : (0 : ℝ) ≤ 80 * (a : ℝ) ^ 2 * (r : ℝ) ^ 2 := by positivity
      rw [hK0r, h7'] at hKr
      linarith
    have : SimpleGraph.extremalNumber n F ≤ G.edgeFinset.card := by
      rw [(hN0 n hn0).1]
      omega
    omega

end WKXGlue

open WangKangXue.SpectralTuran Classical in
/-- **Theorem 1.2** (Wang–Kang–Xue) by reduction to Lemmas 3.1, 3.7, 3.8 and 3.10. -/
theorem solution {W : Type*} [Fintype W] (F : SimpleGraph W) (r a : ℕ) (hr : 2 ≤ r)
    (hF : TuranPlusEdges F r a) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ G : SimpleGraph (Fin n), IsSpectralExtremal F G →
      G.edgeFinset.card = SimpleGraph.extremalNumber n F :=
  wkx_glue2 F r a hr hF (lemma_3_1 F r a hr hF) (lemma_3_7 F r a hr hF)
    (fun ha => lemma_3_8 F r a hr ha hF) (lemma_3_10 F r a hr hF)
