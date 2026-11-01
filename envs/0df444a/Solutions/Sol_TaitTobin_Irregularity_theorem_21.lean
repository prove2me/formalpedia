-- Prove2me | solution 1 for TaitTobin.Irregularity.theorem_21
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-31T13:16:21.013968+00:00
-- url     : https://prove2.me/submissions/2346ca96-9141-44c3-8945-4590a949162b

import Mathlib
import Definitions.Def_TaitTobin_Irregularity_Setting

section

open scoped BigOperators RealInnerProductSpace
namespace TaitTobin.Irregularity.Fresh

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma eigenbasis_action (T : E →ₗ[ℝ] E) (b : OrthonormalBasis ι ℝ E)
    (e : ι → ℝ) (he : ∀ i, T (b i) = e i • b i) (v : E) :
    T v = ∑ i, (⟪b i, v⟫ * e i) • b i := by
  conv_lhs => rw [← b.sum_repr' v]
  simp only [map_sum, map_smul, he, smul_smul]

lemma eigenbasis_quadratic (T : E →ₗ[ℝ] E) (b : OrthonormalBasis ι ℝ E)
    (e : ι → ℝ) (he : ∀ i, T (b i) = e i • b i) (v : E) :
    ⟪v, T v⟫ = ∑ i, e i * ⟪b i, v⟫ ^ 2 := by
  rw [eigenbasis_action T b e he v, inner_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [inner_smul_right, real_inner_comm v (b i)]
  ring

lemma eigenbasis_rayleigh (T : E →ₗ[ℝ] E) (b : OrthonormalBasis ι ℝ E)
    (e : ι → ℝ) (he : ∀ i, T (b i) = e i • b i)
    (lam : ℝ) (hl : ∀ i, e i ≤ lam) (v : E) :
    ⟪v, T v⟫ ≤ lam * ‖v‖ ^ 2 := by
  rw [eigenbasis_quadratic T b e he v, ← b.sum_sq_inner_right v, Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hl i) (sq_nonneg _)

lemma eigenbasis_rayleigh_eq (T : E →ₗ[ℝ] E) (b : OrthonormalBasis ι ℝ E)
    (e : ι → ℝ) (he : ∀ i, T (b i) = e i • b i)
    (lam : ℝ) (hl : ∀ i, e i ≤ lam) (v : E)
    (hv : ⟪v, T v⟫ = lam * ‖v‖ ^ 2) : T v = lam • v := by
  have hz : ∑ i, (lam - e i) * ⟪b i, v⟫ ^ 2 = 0 := by
    rw [eigenbasis_quadratic T b e he v, ← b.sum_sq_inner_right v, Finset.mul_sum] at hv
    simp only [sub_mul, Finset.sum_sub_distrib]
    linarith
  have hi (i : ι) : (lam - e i) * ⟪b i, v⟫ ^ 2 = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => mul_nonneg (sub_nonneg.mpr (hl j)) (sq_nonneg _))).mp hz i (Finset.mem_univ i)
  have hc (i : ι) : ⟪b i, v⟫ * e i = lam * ⟪b i, v⟫ := by
    rcases mul_eq_zero.mp (hi i) with h | h
    · have : lam = e i := sub_eq_zero.mp h
      rw [this, mul_comm]
    · have : ⟪b i, v⟫ = 0 := (sq_eq_zero_iff).mp h
      simp [this]
  rw [eigenbasis_action T b e he v]
  conv_rhs => rw [← b.sum_repr' v]
  simp only [Finset.smul_sum, smul_smul, hc]

end TaitTobin.Irregularity.Fresh
end

section

open scoped BigOperators Matrix Classical
open WangKangXue.SpectralTuran
namespace TaitTobin.Irregularity.Fresh

variable {V : Type*} [Fintype V]

noncomputable def adjSum (G : SimpleGraph V) (v : V → ℝ) (i : V) : ℝ := by
  classical
  exact ∑ j, if G.Adj i j then v j else 0

noncomputable def quad (G : SimpleGraph V) (v : V → ℝ) : ℝ := by
  classical
  exact ∑ i, ∑ j, if G.Adj i j then v i * v j else 0

def sqnorm (v : V → ℝ) : ℝ := ∑ i, v i ^ 2

lemma quad_eq_sum (G : SimpleGraph V) (v : V → ℝ) :
    quad G v = ∑ i, v i * adjSum G v i := by
  classical
  simp [quad, adjSum, Finset.mul_sum, mul_ite]

lemma adjSum_eq_mulVec (G : SimpleGraph V) (v : V → ℝ) :
    adjSum G v = (G.adjMatrix ℝ) *ᵥ v := by
  classical
  ext i
  simp [adjSum, Matrix.mulVec, dotProduct, SimpleGraph.adjMatrix_apply]

lemma quad_eq_dot (G : SimpleGraph V) (v : V → ℝ) :
    quad G v = v ⬝ᵥ ((G.adjMatrix ℝ) *ᵥ v) := by
  classical
  rw [quad_eq_sum, adjSum_eq_mulVec]
  rfl

lemma sqnorm_nonneg (v : V → ℝ) : 0 ≤ sqnorm v :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

lemma sqnorm_pos {v : V → ℝ} (hv : v ≠ 0) : 0 < sqnorm v := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra h
    push Not at h
    exact hv (funext h)
  exact Finset.sum_pos' (fun _ _ => sq_nonneg _) ⟨i, Finset.mem_univ i, sq_pos_of_ne_zero hi⟩

lemma quad_eigen (G : SimpleGraph V) (v : V → ℝ) (lam : ℝ)
    (he : ∀ i, adjSum G v i = lam * v i) : quad G v = lam * sqnorm v := by
  rw [quad_eq_sum]
  simp only [he, sqnorm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma quad_abs_le (G : SimpleGraph V) (v : V → ℝ) :
    quad G v ≤ quad G (fun i => |v i|) := by
  classical
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  split_ifs
  · rw [← abs_mul]
    exact le_abs_self _
  · rfl

lemma sqnorm_abs (v : V → ℝ) : sqnorm (fun i => |v i|) = sqnorm v := by
  simp [sqnorm, sq_abs]

end TaitTobin.Irregularity.Fresh
end

section

open scoped BigOperators Matrix Classical RealInnerProductSpace
open WangKangXue.SpectralTuran
namespace TaitTobin.Irregularity.Fresh

variable {V : Type*} [Fintype V] [DecidableEq V]

lemma adj_eigenbasis_action (G : SimpleGraph V) (i : V) :
    (Matrix.toLpLin 2 2 (G.adjMatrix ℝ)) ((G.isHermitian_adjMatrix ℝ).eigenvectorBasis i) =
      (G.isHermitian_adjMatrix ℝ).eigenvalues i • (G.isHermitian_adjMatrix ℝ).eigenvectorBasis i := by
  apply PiLp.ext
  intro j
  exact congrFun ((G.isHermitian_adjMatrix ℝ).mulVec_eigenvectorBasis i) j

lemma eigenvalue_le_specRad (G : SimpleGraph V) (i : V) :
    (G.isHermitian_adjMatrix ℝ).eigenvalues i ≤ specRad G := by
  have hn : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨i⟩
  simp only [specRad, dif_pos hn, Matrix.IsHermitian.eigenvalues]
  exact (G.isHermitian_adjMatrix ℝ).eigenvalues₀_antitone (show (⟨0, hn⟩ : Fin (Fintype.card V)) ≤ _ from Nat.zero_le _)

lemma euclidean_quad (G : SimpleGraph V) (v : V → ℝ) :
    ⟪(WithLp.toLp 2 v : EuclideanSpace ℝ V),
      Matrix.toLpLin 2 2 (G.adjMatrix ℝ) (WithLp.toLp 2 v)⟫ = quad G v := by
  rw [quad_eq_dot]
  simp [Matrix.toLpLin_apply, EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]

omit [DecidableEq V] in
lemma euclidean_sqnorm (v : V → ℝ) :
    ‖(WithLp.toLp 2 v : EuclideanSpace ℝ V)‖ ^ 2 = sqnorm v := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [sqnorm, Real.norm_eq_abs, sq_abs]

lemma rayleigh_bound (G : SimpleGraph V) (v : V → ℝ) :
    quad G v ≤ specRad G * sqnorm v := by
  have h := eigenbasis_rayleigh (Matrix.toLpLin 2 2 (G.adjMatrix ℝ))
    (G.isHermitian_adjMatrix ℝ).eigenvectorBasis (G.isHermitian_adjMatrix ℝ).eigenvalues
    (adj_eigenbasis_action G) (specRad G) (eigenvalue_le_specRad G)
    (WithLp.toLp 2 v)
  simpa only [euclidean_quad, euclidean_sqnorm] using h

lemma rayleigh_eq_eigen (G : SimpleGraph V) (v : V → ℝ)
    (hv : quad G v = specRad G * sqnorm v) :
    ∀ i, adjSum G v i = specRad G * v i := by
  have h := eigenbasis_rayleigh_eq (Matrix.toLpLin 2 2 (G.adjMatrix ℝ))
    (G.isHermitian_adjMatrix ℝ).eigenvectorBasis (G.isHermitian_adjMatrix ℝ).eigenvalues
    (adj_eigenbasis_action G) (specRad G) (eigenvalue_le_specRad G)
    (WithLp.toLp 2 v) (by simpa only [euclidean_quad, euclidean_sqnorm] using hv)
  intro i
  rw [adjSum_eq_mulVec]
  exact congrArg (fun z : EuclideanSpace ℝ V => z i) h

lemma exists_top_vector (G : SimpleGraph V) (hn : 0 < Fintype.card V) :
    ∃ v : V → ℝ, v ≠ 0 ∧ ∀ i, adjSum G v i = specRad G * v i := by
  let j : V := Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card V)) ⟨0, hn⟩
  let b := (G.isHermitian_adjMatrix ℝ).eigenvectorBasis
  refine ⟨fun i => b j i, ?_, ?_⟩
  · intro h
    have hb : b j = 0 := by
      apply PiLp.ext
      intro i
      exact congrFun h i
    exact b.orthonormal.ne_zero j hb
  · have hj : (G.isHermitian_adjMatrix ℝ).eigenvalues j = specRad G := by
      simp [Matrix.IsHermitian.eigenvalues, j, specRad, hn]
    intro i
    rw [adjSum_eq_mulVec]
    have h := congrFun ((G.isHermitian_adjMatrix ℝ).mulVec_eigenvectorBasis j) i
    simpa only [hj, Pi.smul_apply, smul_eq_mul] using h

end TaitTobin.Irregularity.Fresh
end

section

open scoped BigOperators Classical
open WangKangXue.SpectralTuran
namespace TaitTobin.Irregularity.Fresh

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
lemma nonnegative_eigen_zero_neighbor (G : SimpleGraph V) (v : V → ℝ) (lam : ℝ)
    (hv : ∀ i, 0 ≤ v i) (he : ∀ i, adjSum G v i = lam * v i)
    {i j : V} (hij : G.Adj i j) (hi : v i = 0) : v j = 0 := by
  have hs : ∑ k, (if G.Adj i k then v k else 0) = 0 := by
    simpa [adjSum, hi] using he i
  have hj := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => by split_ifs; exact hv k; exact le_rfl)).mp hs j (Finset.mem_univ j)
  simpa [hij] using hj

omit [DecidableEq V] in
lemma nonnegative_eigen_zero_walk (G : SimpleGraph V) (v : V → ℝ) (lam : ℝ)
    (hv : ∀ i, 0 ≤ v i) (he : ∀ i, adjSum G v i = lam * v i)
    {i j : V} (p : G.Walk i j) (hi : v i = 0) : v j = 0 := by
  induction p with
  | nil => exact hi
  | @cons i j k hij p ih =>
    exact ih (nonnegative_eigen_zero_neighbor G v lam hv he hij hi)

lemma exists_positive_top_vector (G : SimpleGraph V) (hG : G.Connected)
    (hn : 0 < Fintype.card V) :
    ∃ v : V → ℝ, (∀ i, 0 < v i) ∧ (∀ i, v i ≤ 1) ∧
      (∃ x, v x = 1) ∧ ∀ i, adjSum G v i = specRad G * v i := by
  obtain ⟨a, ha, he⟩ := exists_top_vector G hn
  let b : V → ℝ := fun i => |a i|
  have hq : quad G b = specRad G * sqnorm b := by
    apply le_antisymm (rayleigh_bound G b)
    rw [show sqnorm b = sqnorm a from sqnorm_abs a, ← quad_eigen G a (specRad G) he]
    exact quad_abs_le G a
  have hbE := rayleigh_eq_eigen G b hq
  have hb0 (i : V) : 0 ≤ b i := abs_nonneg _
  have hbp (i : V) : 0 < b i := by
    by_contra h
    have hi : b i = 0 := le_antisymm (le_of_not_gt h) (hb0 i)
    have hbz (j : V) : b j = 0 := by
      obtain ⟨p⟩ := hG i j
      exact nonnegative_eigen_zero_walk G b (specRad G) hb0 hbE p hi
    apply ha
    funext j
    exact abs_eq_zero.mp (hbz j)
  have hne : (Finset.univ : Finset V).Nonempty := Finset.univ_nonempty_iff.mpr (Fintype.card_pos_iff.mp hn)
  obtain ⟨x, _, hx⟩ := Finset.exists_max_image Finset.univ b hne
  refine ⟨fun i => b i / b x, ?_, ?_, ⟨x, div_self (hbp x).ne'⟩, ?_⟩
  · intro i
    exact div_pos (hbp i) (hbp x)
  · intro i
    exact (div_le_one (hbp x)).mpr (hx i (Finset.mem_univ i))
  · intro i
    have hs : adjSum G (fun j => b j / b x) i = adjSum G b i / b x := by
      simp [adjSum, Finset.sum_div, ite_div]
    rw [hs, hbE i]
    ring

end TaitTobin.Irregularity.Fresh
end

section

open SimpleGraph Finset
open scoped Classical

namespace TaitTobin.Irregularity.Fresh

variable {V : Type*}

def addEdge (G : SimpleGraph V) (u v : V) : SimpleGraph V := G ⊔ SimpleGraph.edge u v

def eraseEdge (G : SimpleGraph V) (u v : V) : SimpleGraph V := G.deleteEdges {s(u,v)}

lemma addEdge_adj (G : SimpleGraph V) (u v i j : V) :
    (addEdge G u v).Adj i j ↔ G.Adj i j ∨
      ((i = u ∧ j = v ∨ i = v ∧ j = u) ∧ i ≠ j) := by
  simp only [addEdge, sup_adj, SimpleGraph.edge_adj]

lemma eraseEdge_adj (G : SimpleGraph V) (u v i j : V) :
    (eraseEdge G u v).Adj i j ↔ G.Adj i j ∧
      ¬ (i = u ∧ j = v ∨ i = v ∧ j = u) := by
  simp only [eraseEdge, deleteEdges_adj, Set.mem_singleton_iff, Sym2.eq_iff]

lemma connected_addEdge {G : SimpleGraph V} (hG : G.Connected) (u v : V) :
    (addEdge G u v).Connected := hG.mono le_sup_left

lemma eraseEdge_connected_of_universal {G : SimpleGraph V} (hG : G.Connected)
    {x u v : V} (hx : ∀ i, i ≠ x → G.Adj i x) (hu : u ≠ x) (hv : v ≠ x) :
    (eraseEdge G u v).Connected := by
  apply hG.connected_delete_edge_of_not_isBridge
  rw [isBridge_iff]
  intro hn
  apply hn
  have hux : (eraseEdge G u v).Adj u x := by
    rw [eraseEdge_adj]
    exact ⟨hx u hu, by tauto⟩
  have hxv : (eraseEdge G u v).Adj x v := by
    rw [eraseEdge_adj]
    exact ⟨(hx v hv).symm, by tauto⟩
  exact hux.reachable.trans hxv.reachable

end TaitTobin.Irregularity.Fresh
end

section

open SimpleGraph

namespace TaitTobin.Irregularity.Fresh

variable {V : Type*}

lemma exists_connected_relocation {G : SimpleGraph V} (hG : G.Connected)
    {u x : V} (hux : u ≠ x) (hn : ¬ G.Adj u x) :
    ∃ v, G.Adj u v ∧ v ≠ x ∧ (eraseEdge (addEdge G u x) u v).Connected := by
  obtain ⟨p, hp⟩ := hG.exists_isPath u x
  cases p with
  | nil => exact (hux rfl).elim
  | @cons u v x huv p =>
    have hvx : v ≠ x := fun h => hn (h ▸ huv)
    refine ⟨v, huv, hvx, ?_⟩
    have havoid : s(u,v) ∉ p.edges := by
      intro he
      exact (Walk.cons_isPath_iff huv p).mp hp |>.2 (p.fst_mem_support_of_mem_edges he)
    have ht : (eraseEdge G u v).Reachable v x :=
      (p.toDeleteEdges {s(u,v)} (by
        intro e he hs
        have heq : e = s(u,v) := Set.mem_singleton_iff.mp hs
        exact havoid (heq ▸ he))).reachable
    have hle : eraseEdge G u v ≤ eraseEdge (addEdge G u x) u v :=
      deleteEdges_mono le_sup_left
    apply (connected_addEdge hG u x).connected_delete_edge_of_not_isBridge
    rw [isBridge_iff]
    intro hbridge
    apply hbridge
    have hnew : (eraseEdge (addEdge G u x) u v).Adj u x := by
      rw [eraseEdge_adj, addEdge_adj]
      exact ⟨Or.inr ⟨Or.inl ⟨rfl, rfl⟩, hux⟩, by tauto⟩
    exact hnew.reachable.trans (ht.mono hle).symm

end TaitTobin.Irregularity.Fresh
end

section

open SimpleGraph Finset
open scoped Classical

namespace TaitTobin.Irregularity.Fresh

variable {V : Type*} [Fintype V]

lemma adjSum_addEdge {G : SimpleGraph V} {u v : V} (huv : u ≠ v) (hn : ¬ G.Adj u v)
    (w : V → ℝ) (i : V) :
    adjSum (addEdge G u v) w i = adjSum G w i +
      (if i = u then w v else 0) + (if i = v then w u else 0) := by
  classical
  have hh : ∀ j, (if (addEdge G u v).Adj i j then w j else 0) =
      (if G.Adj i j then w j else 0) +
      (if i = u then (if j = v then w v else 0) else 0) +
      (if i = v then (if j = u then w u else 0) else 0) := by
    intro j
    have hnv : ¬ G.Adj v u := fun h => hn h.symm
    by_cases hiu : i = u <;> by_cases hiv : i = v <;>
      by_cases hju : j = u <;> by_cases hjv : j = v <;>
      simp_all [addEdge_adj]
  unfold adjSum
  simp_rw [hh]
  simp [Finset.sum_add_distrib]

lemma quad_addEdge {G : SimpleGraph V} {u v : V} (huv : u ≠ v) (hn : ¬ G.Adj u v)
    (w : V → ℝ) : quad (addEdge G u v) w = quad G w + 2 * w u * w v := by
  classical
  rw [quad_eq_sum, quad_eq_sum]
  simp_rw [adjSum_addEdge huv hn, mul_add]
  simp only [Finset.sum_add_distrib, mul_ite, mul_zero]
  simp
  ring

omit [Fintype V] in
lemma add_eraseEdge {G : SimpleGraph V} {u v : V} (huv : G.Adj u v) :
    addEdge (eraseEdge G u v) u v = G := by
  ext i j
  rw [addEdge_adj, eraseEdge_adj]
  constructor
  · rintro (h | ⟨h, _⟩)
    · exact h.1
    · rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact huv
      · exact huv.symm
  · intro hij
    by_cases h : i = u ∧ j = v ∨ i = v ∧ j = u
    · exact Or.inr ⟨h, hij.ne⟩
    · exact Or.inl ⟨hij, h⟩

lemma adjSum_eraseEdge {G : SimpleGraph V} {u v : V} (huv : G.Adj u v)
    (w : V → ℝ) (i : V) :
    adjSum G w i = adjSum (eraseEdge G u v) w i +
      (if i = u then w v else 0) + (if i = v then w u else 0) := by
  have hn : ¬ (eraseEdge G u v).Adj u v := by simp [eraseEdge_adj]
  have hh := adjSum_addEdge huv.ne hn w i
  rwa [add_eraseEdge huv] at hh

lemma quad_eraseEdge {G : SimpleGraph V} {u v : V} (huv : G.Adj u v)
    (w : V → ℝ) : quad G w = quad (eraseEdge G u v) w + 2 * w u * w v := by
  have hn : ¬ (eraseEdge G u v).Adj u v := by simp [eraseEdge_adj]
  have hh := quad_addEdge huv.ne hn w
  rwa [add_eraseEdge huv] at hh

end TaitTobin.Irregularity.Fresh
end

section

open scoped BigOperators Classical
namespace TaitTobin.Irregularity.Fresh
variable {V : Type*} [Fintype V] [DecidableEq V]

lemma adjSum_erase (G : SimpleGraph V) (v : V → ℝ) (z : V) :
    adjSum G v z = ∑ j ∈ Finset.univ.erase z, if G.Adj z j then v j else 0 := by
  simp [adjSum]

lemma quad_split_vertex (G : SimpleGraph V) (v : V → ℝ) (z : V) :
    quad G v = 2 * v z * adjSum G v z +
      ∑ i ∈ Finset.univ.erase z, ∑ j ∈ Finset.univ.erase z,
        if G.Adj i j then v i * v j else 0 := by
  let a : V → V → ℝ := fun i j => if G.Adj i j then v i * v j else 0
  have ho := Finset.sum_erase_add (Finset.univ : Finset V)
    (fun i => ∑ j, a i j) (Finset.mem_univ z)
  have hi (i : V) := Finset.sum_erase_add (Finset.univ : Finset V)
    (a i) (Finset.mem_univ z)
  have hz : ∑ j, a z j = v z * adjSum G v z := by
    simp [a, adjSum, Finset.mul_sum, mul_ite]
  have hc : ∑ i ∈ Finset.univ.erase z, a i z = v z * adjSum G v z := by
    rw [adjSum_erase, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp only [a, G.adj_comm i z, mul_ite, mul_zero]
    split_ifs <;> ring
  have hs : (∑ i ∈ Finset.univ.erase z, ∑ j, a i j) =
      (∑ i ∈ Finset.univ.erase z, ∑ j ∈ Finset.univ.erase z, a i j) +
      ∑ i ∈ Finset.univ.erase z, a i z := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    exact (hi i).symm
  change (∑ i, ∑ j, a i j) = _
  rw [← ho, hs, hz, hc]
  ring

omit [DecidableEq V] in
lemma adjSum_one (G : SimpleGraph V) (i : V) :
    adjSum G (fun _ => 1) i = (G.degree i : ℝ) := by
  classical
  simp [adjSum, ← G.card_neighborFinset_eq_degree i, SimpleGraph.neighborFinset_def]

omit [DecidableEq V] in
lemma quad_one (G : SimpleGraph V) :
    quad G (fun _ => 1) = 2 * (G.edgeFinset.card : ℝ) := by
  rw [quad_eq_sum]
  simp only [one_mul, adjSum_one]
  exact_mod_cast G.sum_degrees_eq_twice_card_edges

end TaitTobin.Irregularity.Fresh
end

section

open SimpleGraph
open scoped Classical

namespace TaitTobin.Irregularity.Fresh

variable {V : Type*} [Fintype V]

lemma addEdge_card {G : SimpleGraph V} {u v : V} (huv : u ≠ v) (hn : ¬ G.Adj u v) :
    (addEdge G u v).edgeFinset.card = G.edgeFinset.card + 1 := by
  have hh := quad_addEdge huv hn (fun _ => (1 : ℝ))
  rw [quad_one, quad_one] at hh
  have he : ((addEdge G u v).edgeFinset.card : ℝ) = (G.edgeFinset.card : ℝ) + 1 := by
    norm_num at hh
    linarith
  exact_mod_cast he

lemma eraseEdge_card {G : SimpleGraph V} {u v : V} (huv : G.Adj u v) :
    (eraseEdge G u v).edgeFinset.card + 1 = G.edgeFinset.card := by
  have hh := quad_eraseEdge huv (fun _ => (1 : ℝ))
  rw [quad_one, quad_one] at hh
  have he : ((eraseEdge G u v).edgeFinset.card : ℝ) + 1 = (G.edgeFinset.card : ℝ) := by
    norm_num at hh
    linarith
  exact_mod_cast he

end TaitTobin.Irregularity.Fresh
end

section

open SimpleGraph WangKangXue.SpectralTuran
open scoped Classical

namespace TaitTobin.Irregularity.Fresh

lemma universal_max_vertex {n : ℕ} {G : SimpleGraph (Fin n)} (hG : IsIrregMax G)
    {v : Fin n → ℝ} (hv : ∀ i, 0 < v i) (hv1 : ∀ i, v i ≤ 1)
    (he : ∀ i, adjSum G v i = specRad G * v i) {x : Fin n} (hx : v x = 1) :
    ∀ u, u ≠ x → G.Adj u x := by
  intro u hux
  by_contra hn
  obtain ⟨z, huz, hzx, hconn⟩ := exists_connected_relocation hG.1 hux hn
  let A := addEdge G u x
  let H := eraseEdge A u z
  have hauz : A.Adj u z := Or.inl huz
  have hca : A.edgeFinset.card = G.edgeFinset.card + 1 := addEdge_card hux hn
  have hch : H.edgeFinset.card + 1 = A.edgeFinset.card := eraseEdge_card hauz
  have hc : H.edgeFinset.card = G.edgeFinset.card := by omega
  have hlam : specRad H ≤ specRad G := by
    have hh := hG.2 H hconn
    simp only [avgDeg, hc] at hh
    linarith
  have hqa := quad_addEdge hux hn v
  have hqh := quad_eraseEdge hauz v
  have hqg := quad_eigen G v (specRad G) he
  have hgain : 0 ≤ v u * (1 - v z) := mul_nonneg (hv u).le (sub_nonneg.mpr (hv1 z))
  have hge : quad G v ≤ quad H v := by
    change quad A v = quad G v + 2 * v u * v x at hqa
    change quad A v = quad H v + 2 * v u * v z at hqh
    rw [hx] at hqa
    nlinarith
  have hqp : 0 < sqnorm v := sqnorm_pos (by
    intro hz
    have hh := congrFun hz x
    simp only [Pi.zero_apply, hx] at hh
    norm_num at hh)
  have hr := rayleigh_bound H v
  have hlam' : specRad G ≤ specRad H := by nlinarith
  have hleq : specRad H = specRad G := le_antisymm hlam hlam'
  have hqe : quad H v = specRad H * sqnorm v := by
    rw [hleq] at hr ⊢
    linarith
  have heh := rayleigh_eq_eigen H v hqe x
  have hasa : adjSum A v x = adjSum G v x + v u := by
    simpa only [Ne.symm hux, if_false, if_true, add_zero, zero_add] using
      adjSum_addEdge hux hn v x
  have hasd : adjSum A v x = adjSum H v x := by
    simpa only [Ne.symm hux, Ne.symm hzx, if_false, add_zero] using
      adjSum_eraseEdge hauz v x
  rw [hleq] at heh
  have heg := he x
  have hpu := hv u
  linarith

end TaitTobin.Irregularity.Fresh
end

section

open SimpleGraph Finset WangKangXue.SpectralTuran
open scoped Classical

namespace TaitTobin.Irregularity.Fresh

variable {V : Type*} [Fintype V]

lemma adjSum_const (G : SimpleGraph V) (a : ℝ) (i : V) :
    adjSum G (fun _ => a) i = (G.degree i : ℝ) * a := by
  rw [adjSum_eq_mulVec]
  exact G.adjMatrix_mulVec_const_apply

lemma adjSum_mono (G : SimpleGraph V) {v w : V → ℝ} (h : ∀ i, v i ≤ w i) (i : V) :
    adjSum G v i ≤ adjSum G w i := by
  unfold adjSum
  apply Finset.sum_le_sum
  intro j _
  split_ifs
  · exact h j
  · rfl

lemma adjSum_le_degree (G : SimpleGraph V) {v : V → ℝ} (h : ∀ i, v i ≤ 1) (i : V) :
    adjSum G v i ≤ (G.degree i : ℝ) := by
  have hh := adjSum_mono G h i
  simpa only [adjSum_const, mul_one] using hh

lemma sum_adjSum (G : SimpleGraph V) (v : V → ℝ) :
    ∑ i, adjSum G v i = ∑ i, (G.degree i : ℝ) * v i := by
  unfold adjSum
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp_rw [G.adj_comm]
  exact adjSum_const G (v i) i

lemma sum_degree_real (G : SimpleGraph V) :
    ∑ i, (G.degree i : ℝ) = 2 * (G.edgeFinset.card : ℝ) := by
  exact_mod_cast G.sum_degrees_eq_twice_card_edges

lemma sum_at_universal {G : SimpleGraph V} {x : V}
    (hx : ∀ i, i ≠ x → G.Adj i x) (v : V → ℝ) :
    ∑ i, v i = adjSum G v x + v x := by
  have hh : ∀ i, v i = (if G.Adj x i then v i else 0) + (if i = x then v x else 0) := by
    intro i
    by_cases hi : i = x
    · subst i
      simp
    · simp [hi, (hx i hi).symm]
  calc
    ∑ i, v i = ∑ i, ((if G.Adj x i then v i else 0) + (if i = x then v x else 0)) :=
      Finset.sum_congr rfl (fun i _ => hh i)
    _ = adjSum G v x + v x := by simp [adjSum, Finset.sum_add_distrib]

lemma degree_universal {G : SimpleGraph V} {x : V}
    (hx : ∀ i, i ≠ x → G.Adj i x) :
    (G.degree x : ℝ) + 1 = Fintype.card V := by
  have hh := sum_at_universal hx (fun _ => (1 : ℝ))
  simpa only [adjSum_const, mul_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    mul_one] using hh.symm

lemma universal_eigen_sum {G : SimpleGraph V} {x : V} {v : V → ℝ} {l : ℝ}
    (hx : ∀ i, i ≠ x → G.Adj i x) (hvx : v x = 1)
    (he : ∀ i, adjSum G v i = l * v i) : ∑ i, v i = l + 1 := by
  rw [sum_at_universal hx, he, hvx, mul_one]

lemma universal_walk_bound {G : SimpleGraph V} {x : V} {v : V → ℝ} {l : ℝ}
    (hx : ∀ i, i ≠ x → G.Adj i x) (hvx : v x = 1) (hv1 : ∀ i, v i ≤ 1)
    (he : ∀ i, adjSum G v i = l * v i) :
    l ^ 2 ≤ 2 * (G.edgeFinset.card : ℝ) - Fintype.card V + 1 := by
  have he2 : adjSum G (adjSum G v) x = l ^ 2 := by
    change (∑ j, if G.Adj x j then adjSum G v j else 0) = l ^ 2
    simp_rw [he]
    have hf : (∑ j, if G.Adj x j then l * v j else 0) = l * adjSum G v x := by
      simp [adjSum, Finset.mul_sum, mul_ite]
    rw [hf, he, hvx]
    ring
  have hb := adjSum_mono G (adjSum_le_degree G hv1) x
  rw [he2] at hb
  have hs := sum_at_universal hx (fun i => (G.degree i : ℝ))
  rw [sum_degree_real] at hs
  have hd := degree_universal hx
  linarith

end TaitTobin.Irregularity.Fresh
end

section

namespace TaitTobin.Irregularity.Fresh

lemma spectral_scalar_bounds (n l m : ℝ) (hn : 100000000 ≤ n)
    (_hl : 0 ≤ l) (hobj : n / 4 - 4 ≤ l - 2 * m / n)
    (hwalk : l ^ 2 ≤ 2 * m - n + 1) :
    499 * n / 1000 ≤ l ∧ l ≤ 501 * n / 1000 ∧ 0 < l := by
  have hn0 : 0 < n := by linarith
  have hm : 2 * m ≤ (l - (n / 4 - 4)) * n := by
    apply (div_le_iff₀ hn0).mp
    linarith
  have hcenter : (l - n / 2) ^ 2 ≤ 3 * n + 1 := by nlinarith
  have hn2 : 100000000 * n ≤ n ^ 2 := by
    nlinarith [mul_nonneg hn0.le (sub_nonneg.mpr hn)]
  have hlo : 499 * n / 1000 ≤ l := by
    by_contra h
    have hh : l < 499 * n / 1000 := lt_of_not_ge h
    have hs := sq_nonneg (l - 499 * n / 1000)
    nlinarith
  have hhi : l ≤ 501 * n / 1000 := by
    by_contra h
    have hh : 501 * n / 1000 < l := lt_of_not_ge h
    have hs := sq_nonneg (l - 501 * n / 1000)
    nlinarith
  exact ⟨hlo, hhi, by linarith⟩

lemma mass_scalar_bounds (n l D Q : ℝ) (hn : 100000000 ≤ n)
    (hlo : 499 * n / 1000 ≤ l) (hhi : l ≤ 501 * n / 1000)
    (hD0 : 0 ≤ D) (hD : l * D ≤ 4 * n) (hQ : Q = l + 1 - D) :
    D ≤ 9 ∧ 498 * n / 1000 ≤ Q ∧ Q ≤ 502 * n / 1000 := by
  have hn0 : 0 < n := by linarith
  have hl0 : 0 < l := by linarith
  have hD9 : D ≤ 9 := by
    by_contra h
    have hh : 9 < D := lt_of_not_ge h
    have hm := mul_lt_mul_of_pos_left hh hl0
    nlinarith
  exact ⟨hD9, by linarith, by linarith⟩

lemma clique_scalar_bounds (n l u : ℝ) (hn : 100000000 ≤ n)
    (hlo : 499 * n / 1000 ≤ l) (hhi : l ≤ 501 * n / 1000)
    (hu0 : l - 89 ≤ u) (hu1 : u ≤ l + 11) :
    49 * n / 100 ≤ u ∧ u ≤ 51 * n / 100 := by
  constructor <;> linarith

lemma clique_entry_scalar_bound (n l v : ℝ) (hn : 100000000 ≤ n)
    (hlo : 499 * n / 1000 ≤ l) (_hv : v ≤ 1)
    (hd : l * (1 - v) ≤ 91) : 99 / 100 ≤ v := by
  by_contra h
  have hh : v < 99 / 100 := lt_of_not_ge h
  have hl : 0 < l := by linarith
  have hm := mul_lt_mul_of_pos_left (show 1 / 100 < 1 - v by linarith) hl
  nlinarith

lemma intermediate_gain_scalar (n l Q z S u deg : ℝ) (hn : 100000000 ≤ n)
    (_hl0 : 0 ≤ l) (hl1 : l ≤ 51 * n / 100)
    (hQ0 : 498 * n / 1000 ≤ Q) (hQ1 : Q ≤ 51 * n / 100)
    (hz0 : 49 / 100 ≤ z) (hz1 : z ≤ 51 / 100)
    (hS : 49 * 99 * n / 10000 ≤ S)
    (hu : u ≤ 51 * n / 100) (hdeg : 49 ^ 2 * n / 10000 ≤ deg) :
    3 / 5 < (2 * S - l * (1 + z ^ 2)) / (Q + 1 - z ^ 2) ∧
    2 * (u - deg) / n ≤ 2699 / 5000 := by
  have hn0 : 0 < n := by linarith
  have hzsq : z ^ 2 ≤ (51 / 100 : ℝ) ^ 2 := by nlinarith
  have hden : 0 < Q + 1 - z ^ 2 := by nlinarith
  have hprod : l * (1 + z ^ 2) ≤ (51 * n / 100) * (1 + (51 / 100) ^ 2) := by
    apply mul_le_mul hl1 (by nlinarith) (by positivity) (by positivity)
  constructor
  · apply (lt_div_iff₀ hden).2
    nlinarith [sq_nonneg z]
  · apply (div_le_iff₀ hn0).2
    linarith

end TaitTobin.Irregularity.Fresh
end

section

open SimpleGraph Finset WangKangXue.SpectralTuran
open scoped Classical

namespace TaitTobin.Irregularity.Fresh

noncomputable def fractionalMass {V : Type*} [Fintype V] (v : V → ℝ) : ℝ :=
  ∑ i, v i * (1 - v i)

lemma fractionalMass_nonneg {V : Type*} [Fintype V] {v : V → ℝ}
    (hv : ∀ i, 0 ≤ v i) (hv1 : ∀ i, v i ≤ 1) : 0 ≤ fractionalMass v :=
  Finset.sum_nonneg fun i _ => mul_nonneg (hv i) (sub_nonneg.mpr (hv1 i))

lemma sqnorm_fractionalMass {V : Type*} [Fintype V] (v : V → ℝ) :
    sqnorm v = (∑ i, v i) - fractionalMass v := by
  unfold sqnorm fractionalMass
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma fractionalMass_bound {n : ℕ} {G : SimpleGraph (Fin n)} {v : Fin n → ℝ} {x : Fin n}
    (hn : 0 < n) (hx : ∀ i, i ≠ x → G.Adj i x) (hvx : v x = 1)
    (hv : ∀ i, 0 ≤ v i) (hv1 : ∀ i, v i ≤ 1) (he : ∀ i, adjSum G v i = specRad G * v i)
    (hobj : (n : ℝ) / 4 - 4 ≤ specRad G - avgDeg G) :
    specRad G * fractionalMass v ≤ 4 * n := by
  have hs := universal_eigen_sum hx hvx he
  have hdeg : (∑ i, (G.degree i : ℝ) * (1 - v i)) =
      2 * G.edgeFinset.card - specRad G * (specRad G + 1) := by
    simp_rw [mul_sub, mul_one]
    rw [Finset.sum_sub_distrib, sum_degree_real, ← sum_adjSum]
    simp_rw [he]
    rw [← Finset.mul_sum, hs]
  have hb : specRad G * fractionalMass v ≤ ∑ i, (G.degree i : ℝ) * (1 - v i) := by
    unfold fractionalMass
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    have hi := adjSum_le_degree G hv1 i
    rw [he] at hi
    calc
      specRad G * (v i * (1 - v i)) = (specRad G * v i) * (1 - v i) := by ring
      _ ≤ (G.degree i : ℝ) * (1 - v i) :=
        mul_le_mul_of_nonneg_right hi (sub_nonneg.mpr (hv1 i))
  rw [hdeg] at hb
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hm : 2 * (G.edgeFinset.card : ℝ) ≤ (specRad G - ((n : ℝ) / 4 - 4)) * n := by
    apply (div_le_iff₀ hn0).mp
    have ho : (n : ℝ) / 4 - 4 ≤ specRad G - 2 * (G.edgeFinset.card : ℝ) / n := by
      simpa only [avgDeg, Fintype.card_fin] using hobj
    linarith
  have hl : 0 ≤ specRad G := by
    have h := he x
    rw [hvx, mul_one] at h
    have hs0 : 0 ≤ adjSum G v x := by
      unfold adjSum
      apply Finset.sum_nonneg
      intro i _
      split_ifs
      · exact hv i
      · rfl
    linarith
  nlinarith [sq_nonneg (specRad G - (n : ℝ) / 2)]

end TaitTobin.Irregularity.Fresh
end

section

open Finset
open scoped Classical

namespace TaitTobin.Irregularity.Fresh

variable {V : Type*} [Fintype V]

noncomputable def highSet (v : V → ℝ) : Finset V := univ.filter (fun i => 9 / 10 ≤ v i)

@[simp] lemma mem_highSet (v : V → ℝ) (i : V) : i ∈ highSet v ↔ 9 / 10 ≤ v i := by
  simp [highSet]

lemma mass_subset_le {v : V → ℝ} (hv : ∀ i, 0 ≤ v i) (hv1 : ∀ i, v i ≤ 1)
    (s : Finset V) : (∑ i ∈ s, v i * (1 - v i)) ≤ fractionalMass v := by
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s)
  intro i _ _
  exact mul_nonneg (hv i) (sub_nonneg.mpr (hv1 i))

lemma highSet_outside_mass {v : V → ℝ} (hv : ∀ i, 0 ≤ v i) (hv1 : ∀ i, v i ≤ 1)
    (hD : fractionalMass v ≤ 9) : (∑ i ∈ (highSet v)ᶜ, v i) ≤ 90 := by
  have hb : (∑ i ∈ (highSet v)ᶜ, v i) ≤
      10 * ∑ i ∈ (highSet v)ᶜ, v i * (1 - v i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    have hn : v i < 9 / 10 := lt_of_not_ge (by simpa using hi)
    have hp := mul_nonneg (hv i) (show 0 ≤ 9 / 10 - v i by linarith)
    nlinarith
  have hm := mass_subset_le hv hv1 (highSet v)ᶜ
  linarith

lemma highSet_deficit {v : V → ℝ} (hv : ∀ i, 0 ≤ v i) (hv1 : ∀ i, v i ≤ 1)
    (hD : fractionalMass v ≤ 9) : (∑ i ∈ highSet v, (1 - v i)) ≤ 10 := by
  have hb : 9 * (∑ i ∈ highSet v, (1 - v i)) ≤
      10 * ∑ i ∈ highSet v, v i * (1 - v i) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    have hn := (mem_highSet v i).mp hi
    have hp := mul_nonneg (show 0 ≤ v i - 9 / 10 by linarith)
      (sub_nonneg.mpr (hv1 i))
    nlinarith
  have hm := mass_subset_le hv hv1 (highSet v)
  linarith

lemma highSet_card_bounds {v : V → ℝ} {l : ℝ}
    (hv : ∀ i, 0 ≤ v i) (hv1 : ∀ i, v i ≤ 1)
    (hD : fractionalMass v ≤ 9) (hs : ∑ i, v i = l + 1) :
    l - 89 ≤ ((highSet v).card : ℝ) ∧ ((highSet v).card : ℝ) ≤ l + 11 := by
  have ho := highSet_outside_mass hv hv1 hD
  have hd := highSet_deficit hv hv1 hD
  have hsplit := (highSet v).sum_add_sum_compl v
  rw [hs] at hsplit
  have hc : (∑ i ∈ highSet v, v i) + (∑ i ∈ highSet v, (1 - v i)) =
      ((highSet v).card : ℝ) := by
    rw [← Finset.sum_add_distrib]
    simp
  have h0 : 0 ≤ ∑ i ∈ (highSet v)ᶜ, v i := Finset.sum_nonneg (fun i _ => hv i)
  have h1 : 0 ≤ ∑ i ∈ highSet v, (1 - v i) :=
    Finset.sum_nonneg (fun i _ => sub_nonneg.mpr (hv1 i))
  constructor <;> linarith

end TaitTobin.Irregularity.Fresh
end

section

open Finset SimpleGraph
open scoped Classical

namespace TaitTobin.Irregularity.Fresh

variable {V : Type*} [Fintype V]

lemma sum_neighbors_le {G : SimpleGraph V} {v : V → ℝ} (hv : ∀ i, 0 ≤ v i)
    (s : Finset V) (i : V) (hs : ∀ j ∈ s, G.Adj i j) :
    (∑ j ∈ s, v j) ≤ adjSum G v i := by
  have hh : (∑ j ∈ s, v j) = ∑ j ∈ s, if G.Adj i j then v j else 0 := by
    apply Finset.sum_congr rfl
    intro j hj
    simp only [hs j hj, if_true]
  rw [hh]
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s)
  intro j _ _
  split_ifs
  · exact hv j
  · rfl

lemma clique_sum_le_adjSum {G : SimpleGraph V} {v : V → ℝ} (hv : ∀ i, 0 ≤ v i)
    (s : Finset V) {i : V} (hi : i ∈ s)
    (hs : ∀ j ∈ s, i ≠ j → G.Adj i j) :
    (∑ j ∈ s, v j) ≤ adjSum G v i + v i := by
  have hh := sum_neighbors_le hv (s.erase i) i (by
    intro j hj
    exact hs j (Finset.mem_erase.mp hj).2 (Finset.mem_erase.mp hj).1.symm)
  have he := Finset.sum_erase_add s v hi
  linarith

end TaitTobin.Irregularity.Fresh
end

section

open SimpleGraph WangKangXue.SpectralTuran
open scoped Classical

namespace TaitTobin.Irregularity.Fresh

lemma high_product_adj {n : ℕ} {G : SimpleGraph (Fin n)} (hG : IsIrregMax G)
    {v : Fin n → ℝ} (he : ∀ i, adjSum G v i = specRad G * v i)
    {i j : Fin n} (hij : i ≠ j) (hp : sqnorm v / n < v i * v j) : G.Adj i j := by
  by_contra hn
  let H := addEdge G i j
  have hc := addEdge_card hij hn
  have hcR : (H.edgeFinset.card : ℝ) = (G.edgeFinset.card : ℝ) + 1 := by
    exact_mod_cast hc
  have hm := hG.2 H (connected_addEdge hG.1 i j)
  have hd : avgDeg H = avgDeg G + 2 / n := by
    simp only [avgDeg, Fintype.card_fin]
    rw [hcR]
    ring
  rw [hd] at hm
  have hl : specRad H ≤ specRad G + 2 / n := by linarith
  have hmul := mul_le_mul_of_nonneg_right hl (sqnorm_nonneg v)
  have hr := rayleigh_bound H v
  have ha := quad_addEdge hij hn v
  have hg := quad_eigen G v (specRad G) he
  change quad H v = quad G v + 2 * v i * v j at ha
  have hnorm : (2 / (n : ℝ)) * sqnorm v = 2 * (sqnorm v / n) := by ring
  nlinarith

lemma low_product_not_adj {n : ℕ} {G : SimpleGraph (Fin n)} (hG : IsIrregMax G)
    {v : Fin n → ℝ} (he : ∀ i, adjSum G v i = specRad G * v i)
    {x : Fin n} (hx : ∀ i, i ≠ x → G.Adj i x)
    {i j : Fin n} (hi : i ≠ x) (hj : j ≠ x) (hp : v i * v j < sqnorm v / n) :
    ¬ G.Adj i j := by
  intro hij
  let H := eraseEdge G i j
  have hc := eraseEdge_card hij
  have hcR : (H.edgeFinset.card : ℝ) + 1 = (G.edgeFinset.card : ℝ) := by
    exact_mod_cast hc
  have hm := hG.2 H (eraseEdge_connected_of_universal hG.1 hx hi hj)
  have hd : avgDeg G = avgDeg H + 2 / n := by
    simp only [avgDeg, Fintype.card_fin]
    rw [← hcR]
    ring
  rw [hd] at hm
  have hl : specRad H ≤ specRad G - 2 / n := by linarith
  have hmul := mul_le_mul_of_nonneg_right hl (sqnorm_nonneg v)
  have hr := rayleigh_bound H v
  have ha := quad_eraseEdge hij v
  have hg := quad_eigen G v (specRad G) he
  change quad G v = quad H v + 2 * v i * v j at ha
  have hnorm : (2 / (n : ℝ)) * sqnorm v = 2 * (sqnorm v / n) := by ring
  nlinarith

end TaitTobin.Irregularity.Fresh
end

section

open Finset SimpleGraph WangKangXue.SpectralTuran
open scoped Classical

namespace TaitTobin.Irregularity.Fresh

lemma highSet_clique {n : ℕ} {G : SimpleGraph (Fin n)} (hG : IsIrregMax G)
    {v : Fin n → ℝ} (he : ∀ i, adjSum G v i = specRad G * v i)
    (hQ : sqnorm v / n ≤ 502 / 1000) :
    ∀ i ∈ highSet v, ∀ j ∈ highSet v, i ≠ j → G.Adj i j := by
  intro i hi j hj hij
  have hi' := (mem_highSet v i).mp hi
  have hj' := (mem_highSet v j).mp hj
  have hp := mul_le_mul hi' hj' (by norm_num : (0 : ℝ) ≤ 9 / 10) (by linarith : 0 ≤ v i)
  apply high_product_adj hG he hij
  nlinarith

lemma highSet_entries {n : ℕ} (hn : 100000000 ≤ n) {G : SimpleGraph (Fin n)}
    {v : Fin n → ℝ} (hv : ∀ i, 0 ≤ v i) (hv1 : ∀ i, v i ≤ 1)
    (he : ∀ i, adjSum G v i = specRad G * v i)
    (hl : 499 * (n : ℝ) / 1000 ≤ specRad G) (hD : fractionalMass v ≤ 9)
    (hs : ∑ i, v i = specRad G + 1)
    (hcl : ∀ i ∈ highSet v, ∀ j ∈ highSet v, i ≠ j → G.Adj i j) :
    ∀ i ∈ highSet v, 99 / 100 ≤ v i := by
  intro i hi
  have ho := highSet_outside_mass hv hv1 hD
  have hdec : (fun a b : Fin n => Classical.propDecidable (a = b)) =
      (inferInstance : DecidableEq (Fin n)) := Subsingleton.elim _ _
  rw [hdec] at ho
  have hsplit := (highSet v).sum_add_sum_compl v
  rw [hs] at hsplit
  have hc := clique_sum_le_adjSum hv (highSet v) hi (hcl i hi)
  rw [he] at hc
  have hspl : (∑ j ∈ highSet v, v j) + (∑ j ∈ (highSet v)ᶜ, v j) = specRad G + 1 := by
    simpa using! hsplit
  have hout : (∑ j ∈ (highSet v)ᶜ, v j) ≤ 90 := by simpa using! ho
  have hneigh : (∑ j ∈ highSet v, v j) ≤ specRad G * v i + v i := by simpa using! hc
  have hd : specRad G * (1 - v i) ≤ 91 := by
    have hvi := hv1 i
    nlinarith only [hspl, hout, hneigh, hvi]
  apply clique_entry_scalar_bound (n : ℝ) (specRad G) (v i) (by exact_mod_cast hn) hl (hv1 i) hd

lemma outside_highSet_le {n : ℕ} (hn : 100000000 ≤ n) {G : SimpleGraph (Fin n)}
    (hG : IsIrregMax G) {v : Fin n → ℝ} (hv : ∀ i, 0 ≤ v i) (hv1 : ∀ i, v i ≤ 1)
    (he : ∀ i, adjSum G v i = specRad G * v i)
    (hl : 499 * (n : ℝ) / 1000 ≤ specRad G) (hD : fractionalMass v ≤ 9)
    (hs : ∑ i, v i = specRad G + 1) (hQ : sqnorm v / n ≤ 502 / 1000)
    (hU : ∀ i ∈ highSet v, 99 / 100 ≤ v i) :
    ∀ z ∉ highSet v, v z ≤ 51 / 100 := by
  intro z hz
  by_contra hh
  have hzl : 51 / 100 < v z := lt_of_not_ge hh
  have hadj : ∀ i ∈ highSet v, G.Adj z i := by
    intro i hi
    have hzi : z ≠ i := by intro h; exact hz (h ▸ hi)
    apply high_product_adj hG he hzi
    have hp := mul_le_mul (le_of_lt hzl) (hU i hi) (by norm_num : (0 : ℝ) ≤ 99 / 100) (hv z)
    nlinarith
  have hsum := sum_neighbors_le hv (highSet v) z hadj
  rw [he] at hsum
  have ho := highSet_outside_mass hv hv1 hD
  have hdec : (fun a b : Fin n => Classical.propDecidable (a = b)) =
      (inferInstance : DecidableEq (Fin n)) := Subsingleton.elim _ _
  rw [hdec] at ho
  have hsplit := (highSet v).sum_add_sum_compl v
  rw [hs] at hsplit
  have hz9 : v z < 9 / 10 := lt_of_not_ge (by simpa using hz)
  have hnR : (100000000 : ℝ) ≤ n := by exact_mod_cast hn
  have hlp : 0 < specRad G := by linarith
  have hm := mul_lt_mul_of_pos_left hz9 hlp
  have hspl : (∑ j ∈ highSet v, v j) + (∑ j ∈ (highSet v)ᶜ, v j) = specRad G + 1 := by
    simpa using! hsplit
  have hout : (∑ j ∈ (highSet v)ᶜ, v j) ≤ 90 := by simpa using! ho
  have hneigh : (∑ j ∈ highSet v, v j) ≤ specRad G * v z := by simpa using! hsum
  nlinarith only [hspl, hout, hneigh, hm, hl, hnR]

end TaitTobin.Irregularity.Fresh
end

section

open scoped BigOperators Classical
open WangKangXue.SpectralTuran
namespace TaitTobin.Irregularity.Fresh
variable {V : Type*} [Fintype V] [DecidableEq V]

def comparisonGraph (S : Finset V) (x : V) : SimpleGraph V where
  Adj i j := i ≠ j ∧ ((i ∈ S ∧ j ∈ S) ∨ i = x ∨ j = x)
  symm := ⟨by intro i j h; exact ⟨Ne.symm h.1, by tauto⟩⟩
  loopless := ⟨by intro i h; exact h.1 rfl⟩

omit [Fintype V] in
lemma comparison_connected (S : Finset V) (x : V) : (comparisonGraph S x).Connected := by
  apply (SimpleGraph.connected_iff_exists_forall_reachable _).2
  refine ⟨x, fun y => ?_⟩
  by_cases h : x = y
  · subst y; exact SimpleGraph.Reachable.refl _
  · exact SimpleGraph.Adj.reachable (show (comparisonGraph S x).Adj x y from ⟨h, Or.inr (Or.inl rfl)⟩)

lemma comparison_degree_bound (S : Finset V) (x i : V) (hx : x ∈ S) :
    (comparisonGraph S x).degree i ≤
      (if i ∈ S then S.card else 0) + (if i = x then Fintype.card V else 1) := by
  classical
  by_cases hi : i = x
  · subst i
    have h := ((comparisonGraph S x).degree_lt_card_verts x).le
    simp only [hx, if_true]
    omega
  · by_cases hs : i ∈ S
    · have hsub : (comparisonGraph S x).neighborFinset i ⊆ S := by
        intro j hj
        have h := (SimpleGraph.mem_neighborFinset _ _ _).mp hj
        rcases h.2 with h | h | h
        · exact h.2
        · exact False.elim (hi h)
        · simpa only [h] using hx
      have h := Finset.card_le_card hsub
      simpa only [SimpleGraph.card_neighborFinset_eq_degree, hs, hi, if_true, if_false] using
        (Nat.le_trans h (Nat.le_add_right _ 1))
    · have hsub : (comparisonGraph S x).neighborFinset i ⊆ {x} := by
        intro j hj
        have h := (SimpleGraph.mem_neighborFinset _ _ _).mp hj
        rcases h.2 with h | h | h
        · exact False.elim (hs h.1)
        · exact False.elim (hi h)
        · simpa only [Finset.mem_singleton] using h
      have h := Finset.card_le_card hsub
      simpa only [SimpleGraph.card_neighborFinset_eq_degree, Finset.card_singleton, hs, hi,
        if_true, if_false, zero_add] using h

lemma comparison_edge_bound (S : Finset V) (x : V) (hx : x ∈ S) :
    2 * (comparisonGraph S x).edgeFinset.card ≤ S.card ^ 2 + 2 * Fintype.card V := by
  classical
  rw [← SimpleGraph.sum_degrees_eq_twice_card_edges]
  calc
    _ ≤ ∑ i, ((if i ∈ S then S.card else 0) +
        (if i = x then Fintype.card V else 1)) :=
      Finset.sum_le_sum (fun i _ => comparison_degree_bound S x i hx)
    _ ≤ S.card ^ 2 + 2 * Fintype.card V := by
      rw [Finset.sum_add_distrib]
      have hsum : (∑ i : V, if i ∈ S then S.card else 0) = S.card ^ 2 := by
        simp [pow_two]
      rw [hsum]
      have hb : (∑ i : V, if i = x then Fintype.card V else 1) ≤
          ∑ i : V, ((if i = x then Fintype.card V else 0) + 1) := by
        apply Finset.sum_le_sum
        intro i _
        split_ifs <;> omega
      simpa [Finset.sum_add_distrib, two_mul] using Nat.add_le_add_left hb (S.card ^ 2)

lemma comparison_clique_bound (S : Finset V) (x : V) (hS : S.Nonempty) :
    (S.card : ℝ) - 1 ≤ specRad (comparisonGraph S x) := by
  classical
  let v : V → ℝ := fun i => if i ∈ S then 1 else 0
  have hv : sqnorm v = (S.card : ℝ) := by simp [sqnorm, v]
  have hq : quad (comparisonGraph S x) v = (S.card : ℝ) * ((S.card : ℝ) - 1) := by
    rw [quad_eq_sum]
    have he : ∀ i, v i * adjSum (comparisonGraph S x) v i =
        if i ∈ S then ((S.card : ℝ) - 1) else 0 := by
      intro i
      by_cases hi : i ∈ S
      · have hadj : adjSum (comparisonGraph S x) v i = ((S.erase i).card : ℝ) := by
          unfold adjSum
          have he : ∀ j, (if (comparisonGraph S x).Adj i j then v j else 0) =
              if j ∈ S.erase i then (1 : ℝ) else 0 := by
            intro j
            simp only [comparisonGraph, v, Finset.mem_erase]
            by_cases hj : j ∈ S <;> by_cases hij : i = j <;> simp_all [ne_comm]
          simp only [he]
          rw [Finset.sum_ite_mem_eq]
          simp
        rw [hadj]
        simp [v, hi, Finset.card_erase_of_mem hi, Nat.cast_sub (Finset.one_le_card.mpr hS)]
      · simp [v, hi]
    simp only [he]
    rw [Finset.sum_ite_mem_eq]
    simp
    ring
  have hr := rayleigh_bound (comparisonGraph S x) v
  rw [hq, hv] at hr
  have hp : (0 : ℝ) < S.card := by exact_mod_cast Finset.card_pos.mpr hS
  nlinarith

lemma objective_lower {n : ℕ} (G : SimpleGraph (Fin n)) (hn : 100000000 ≤ n)
    (hG : IsIrregMax G) : (n : ℝ) / 4 - 4 ≤ specRad G - avgDeg G := by
  classical
  obtain ⟨S, _, hS⟩ := Finset.exists_subset_card_eq
    (show n / 2 ≤ (Finset.univ : Finset (Fin n)).card by simp; omega)
  have hp : 0 < n / 2 := by omega
  have hSn : S.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨x, hx⟩ := hSn
  have hc := hG.2 (comparisonGraph S x) (comparison_connected S x)
  have hr := comparison_clique_bound S x ⟨x, hx⟩
  have he := comparison_edge_bound S x hx
  have heR : 2 * ((comparisonGraph S x).edgeFinset.card : ℝ) ≤
      ((n / 2 : ℕ) : ℝ) ^ 2 + 2 * (n : ℝ) := by
    rw [hS, Fintype.card_fin] at he
    exact_mod_cast he
  rw [hS] at hr
  have hnR : (100000000 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have h0 : 2 * ((n / 2 : ℕ) : ℝ) ≤ n := by exact_mod_cast (show 2 * (n / 2) ≤ n by omega)
  have h1 : (n : ℝ) ≤ 2 * ((n / 2 : ℕ) : ℝ) + 1 := by exact_mod_cast (show n ≤ 2 * (n / 2) + 1 by omega)
  have hsq := mul_nonneg (show 0 ≤ (n : ℝ) - 2 * ((n / 2 : ℕ) : ℝ) by linarith)
    (show 0 ≤ 1 - ((n : ℝ) - 2 * ((n / 2 : ℕ) : ℝ)) by linarith)
  have hedge : avgDeg (comparisonGraph S x) ≤ ((n / 2 : ℕ) : ℝ) - 1 - ((n : ℝ) / 4 - 4) := by
    unfold avgDeg
    rw [Fintype.card_fin]
    apply (div_le_iff₀ hn0).2
    nlinarith
  linarith

end TaitTobin.Irregularity.Fresh
end

section

open scoped BigOperators Classical
open WangKangXue.SpectralTuran
namespace TaitTobin.Irregularity.Fresh

lemma extremal_numeric_bounds {n : ℕ} (hn : 100000000 ≤ n)
    (G : SimpleGraph (Fin n)) (hG : IsIrregMax G) (v : Fin n → ℝ) (x : Fin n)
    (hv : ∀ i, 0 ≤ v i) (hv1 : ∀ i, v i ≤ 1) (hx : v x = 1)
    (hu : ∀ i, i ≠ x → G.Adj i x)
    (he : ∀ i, adjSum G v i = specRad G * v i) :
    499 * (n : ℝ) / 1000 ≤ specRad G ∧ specRad G ≤ 501 * (n : ℝ) / 1000 ∧
      0 < specRad G ∧ fractionalMass v ≤ 9 ∧
      498 * (n : ℝ) / 1000 ≤ sqnorm v ∧ sqnorm v ≤ 502 * (n : ℝ) / 1000 := by
  have hnR : (100000000 : ℝ) ≤ n := by exact_mod_cast hn
  have hobj := objective_lower G hn hG
  have hl : 0 ≤ specRad G := by
    have h0 : 0 ≤ adjSum G v x := by
      unfold adjSum
      apply Finset.sum_nonneg
      intro i _
      split_ifs
      · exact hv i
      · rfl
    rw [he x, hx, mul_one] at h0
    exact h0
  have hwalk := universal_walk_bound hu hx hv1 he
  simp only [Fintype.card_fin] at hwalk
  obtain ⟨hl0, hl1, hlp⟩ := spectral_scalar_bounds (n : ℝ) (specRad G) G.edgeFinset.card hnR hl
    (by simpa only [avgDeg, Fintype.card_fin] using hobj) hwalk
  have hmass := fractionalMass_bound (by omega : 0 < n) hu hx hv hv1 he hobj
  have hq : sqnorm v = specRad G + 1 - fractionalMass v := by
    rw [sqnorm_fractionalMass, universal_eigen_sum hu hx he]
  obtain ⟨hD, hQ0, hQ1⟩ := mass_scalar_bounds (n : ℝ) (specRad G) (fractionalMass v) (sqnorm v)
    hnR hl0 hl1 (fractionalMass_nonneg hv hv1) hmass hq
  exact ⟨hl0, hl1, hlp, hD, hQ0, hQ1⟩

end TaitTobin.Irregularity.Fresh
end

section

open scoped BigOperators Classical
namespace TaitTobin.Irregularity.Fresh
variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def completeAt (G : SimpleGraph V) (z : V) (U : Finset V) (hz : z ∉ U) : SimpleGraph V where
  Adj i j := if i = z then j ∈ U else if j = z then i ∈ U else G.Adj i j
  symm := ⟨by
    intro i j
    by_cases hi : i = z <;> by_cases hj : j = z <;> simp_all [G.adj_comm]⟩
  loopless := ⟨by
    intro i
    by_cases hi : i = z <;> simp_all⟩

omit [Fintype V] in
lemma completeAt_mono (G : SimpleGraph V) (z : V) (U : Finset V) (hz : z ∉ U)
    (hN : ∀ i, G.Adj z i → i ∈ U) : G ≤ completeAt G z U hz := by
  intro i j hij
  change (if i = z then j ∈ U else if j = z then i ∈ U else G.Adj i j)
  split_ifs with hi hj
  · subst i
    exact hN j hij
  · subst j
    exact hN i hij.symm
  · exact hij

omit [Fintype V] in
lemma completeAt_connected (G : SimpleGraph V) (z : V) (U : Finset V) (hz : z ∉ U)
    (hN : ∀ i, G.Adj z i → i ∈ U) (hG : G.Connected) :
    (completeAt G z U hz).Connected := hG.mono (completeAt_mono G z U hz hN)

lemma completeAt_adjSum (G : SimpleGraph V) (z : V) (U : Finset V) (hz : z ∉ U)
    (v : V → ℝ) : adjSum (completeAt G z U hz) v z = ∑ i ∈ U, v i := by
  simp [adjSum, completeAt, Finset.sum_ite_mem]

lemma completeAt_quad_update (G : SimpleGraph V) (z : V) (U : Finset V) (hz : z ∉ U)
    (v : V → ℝ) :
    quad (completeAt G z U hz) (Function.update v z 1) =
      quad G v + 2 * (∑ i ∈ U, v i) - 2 * v z * adjSum G v z := by
  rw [quad_split_vertex (completeAt G z U hz) _ z, quad_split_vertex G v z,
    Function.update_self, completeAt_adjSum]
  have hu : (∑ i ∈ U, Function.update v z 1 i) = ∑ i ∈ U, v i := by
    apply Finset.sum_congr rfl
    intro i hi
    have hiz : i ≠ z := by
      intro h
      subst i
      exact hz hi
    exact Function.update_of_ne hiz _ _
  rw [hu]
  have he : (∑ i ∈ Finset.univ.erase z, ∑ j ∈ Finset.univ.erase z,
      if (completeAt G z U hz).Adj i j then Function.update v z 1 i * Function.update v z 1 j else 0) =
      ∑ i ∈ Finset.univ.erase z, ∑ j ∈ Finset.univ.erase z,
        if G.Adj i j then v i * v j else 0 := by
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    simp only [Finset.mem_erase] at hi hj
    simp [completeAt, hi.1, hj.1, Function.update_of_ne]
  rw [he]
  ring

lemma sqnorm_update_one (v : V → ℝ) (z : V) :
    sqnorm (Function.update v z 1) = sqnorm v + 1 - v z ^ 2 := by
  have h1 := Finset.sum_erase_add (Finset.univ : Finset V) (fun i => v i ^ 2) (Finset.mem_univ z)
  have h2 := Finset.sum_erase_add (Finset.univ : Finset V) (fun i => (Function.update v z 1 i) ^ 2) (Finset.mem_univ z)
  have he : (∑ i ∈ Finset.univ.erase z, Function.update v z 1 i ^ 2) =
      ∑ i ∈ Finset.univ.erase z, v i ^ 2 := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [Function.update_of_ne (Finset.mem_erase.mp hi).1]
  rw [he, Function.update_self] at h2
  simp only [sqnorm]
  linarith

lemma completeAt_card (G : SimpleGraph V) (z : V) (U : Finset V) (hz : z ∉ U) :
    ((completeAt G z U hz).edgeFinset.card : ℝ) =
      (G.edgeFinset.card : ℝ) + (U.card : ℝ) - (G.degree z : ℝ) := by
  have h := completeAt_quad_update G z U hz (fun _ => 1)
  have hu : Function.update (fun _ : V => (1 : ℝ)) z 1 = fun _ => 1 := by
    ext i
    simp [Function.update_apply]
  rw [hu, quad_one, quad_one, adjSum_one] at h
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at h
  linarith

end TaitTobin.Irregularity.Fresh
end

section

open scoped BigOperators Classical
open WangKangXue.SpectralTuran
namespace TaitTobin.Irregularity.Fresh

lemma exclude_intermediate {n : ℕ} (hn : 100000000 ≤ n)
    (G : SimpleGraph (Fin n)) (hG : IsIrregMax G) (v : Fin n → ℝ)
    (_hv0 : ∀ i, 0 ≤ v i) (hv1 : ∀ i, v i ≤ 1)
    (he : ∀ i, adjSum G v i = specRad G * v i)
    (hl0 : 499 * (n : ℝ) / 1000 ≤ specRad G)
    (hl1 : specRad G ≤ 501 * (n : ℝ) / 1000)
    (hQ0 : 498 * (n : ℝ) / 1000 ≤ sqnorm v)
    (hQ1 : sqnorm v ≤ 502 * (n : ℝ) / 1000)
    (U : Finset (Fin n)) (hu0 : 49 * (n : ℝ) / 100 ≤ U.card)
    (hu1 : (U.card : ℝ) ≤ 51 * n / 100) (huv : ∀ i ∈ U, 99 / 100 ≤ v i)
    (z : Fin n) (hz : z ∉ U) (hz0 : 49 / 100 ≤ v z) (hz1 : v z ≤ 51 / 100)
    (hN : ∀ i, G.Adj z i → i ∈ U) : False := by
  let H := completeAt G z U hz
  have hnR : (100000000 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : 0 < (n : ℝ) := by linarith
  have hl : 0 ≤ specRad G := by linarith
  have hd : specRad G * v z ≤ (G.degree z : ℝ) := by
    rw [← he z, ← adjSum_one G z]
    apply Finset.sum_le_sum
    intro i _
    split_ifs <;> first | exact hv1 i | exact le_rfl
  have hdeg : 49 ^ 2 * (n : ℝ) / 10000 ≤ (G.degree z : ℝ) := by
    have hmul := mul_le_mul (show 49 * (n : ℝ) / 100 ≤ specRad G by linarith)
      hz0 (by norm_num : (0 : ℝ) ≤ 49 / 100) hl
    nlinarith
  have hS : 49 * 99 * (n : ℝ) / 10000 ≤ ∑ i ∈ U, v i := by
    have hs : (U.card : ℝ) * (99 / 100) ≤ ∑ i ∈ U, v i := by
      calc
        _ = ∑ _i ∈ U, (99 / 100 : ℝ) := by simp
        _ ≤ _ := Finset.sum_le_sum huv
    nlinarith
  obtain ⟨hgain, hcost⟩ := intermediate_gain_scalar (n : ℝ) (specRad G) (sqnorm v)
    (v z) (∑ i ∈ U, v i) U.card (G.degree z) hnR hl (by linarith) hQ0
    (by linarith) hz0 hz1 hS hu1 hdeg
  have hden : 0 < sqnorm v + 1 - v z ^ 2 := by nlinarith
  have hr := rayleigh_bound H (Function.update v z 1)
  rw [completeAt_quad_update, quad_eigen G v (specRad G) he, he z, sqnorm_update_one] at hr
  have hquot : (2 * (∑ i ∈ U, v i) - specRad G * (1 + v z ^ 2)) /
      (sqnorm v + 1 - v z ^ 2) ≤ specRad H - specRad G := by
    apply (div_le_iff₀ hden).2
    nlinarith
  have hmax := hG.2 H (completeAt_connected G z U hz hN hG.1)
  have hc := completeAt_card G z U hz
  have hcosteq : avgDeg H - avgDeg G = 2 * ((U.card : ℝ) - G.degree z) / n := by
    simp only [avgDeg, Fintype.card_fin]
    change 2 * ((completeAt G z U hz).edgeFinset.card : ℝ) / n - _ = _
    rw [hc]
    ring
  linarith

end TaitTobin.Irregularity.Fresh
end

section

open SimpleGraph Finset WangKangXue.SpectralTuran
open scoped Classical

namespace TaitTobin.Irregularity.Fresh

lemma extremal_shape {n : ℕ} (hn : 100000000 ≤ n)
    (G : SimpleGraph (Fin n)) (hG : IsIrregMax G) (v : Fin n → ℝ) (x : Fin n)
    (hv : ∀ i, 0 ≤ v i) (hv1 : ∀ i, v i ≤ 1) (hx : v x = 1)
    (hu : ∀ i, i ≠ x → G.Adj i x)
    (he : ∀ i, adjSum G v i = specRad G * v i) :
    x ∈ highSet v ∧ ∀ i j, G.Adj i j ↔ i ≠ j ∧
      ((i ∈ highSet v ∧ j ∈ highSet v) ∨ i = x ∨ j = x) := by
  obtain ⟨hl0, hl1, hlp, hD, hQ0, hQ1⟩ := extremal_numeric_bounds hn G hG v x hv hv1 hx hu he
  have hnR : (100000000 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hq0 : 498 / 1000 ≤ sqnorm v / n := by
    apply (le_div_iff₀ hn0).2
    linarith
  have hq1 : sqnorm v / n ≤ 502 / 1000 := by
    apply (div_le_iff₀ hn0).2
    linarith
  have hxu : x ∈ highSet v := by norm_num [hx]
  have hs := universal_eigen_sum hu hx he
  have hcl := highSet_clique hG he hq1
  have hentries := highSet_entries hn hv hv1 he hl0 hD hs hcl
  have hout := outside_highSet_le hn hG hv hv1 he hl0 hD hs hq1 hentries
  obtain ⟨hc0, hc1⟩ := highSet_card_bounds hv hv1 hD hs
  obtain ⟨hu0, hu1⟩ := clique_scalar_bounds (n : ℝ) (specRad G) (highSet v).card hnR hl0 hl1 hc0 hc1
  have hsmall : ∀ z ∉ highSet v, v z < 49 / 100 := by
    intro z hz
    by_contra hh
    have hz0 : 49 / 100 ≤ v z := le_of_not_gt hh
    have hz1 := hout z hz
    have hzx : z ≠ x := by intro h; exact hz (h.symm ▸ hxu)
    apply exclude_intermediate hn G hG v hv hv1 he hl0 hl1 hQ0 hQ1
      (highSet v) hu0 hu1 hentries z hz hz0 hz1
    intro i hzi
    by_contra hi
    have hi1 := hout i hi
    have hix : i ≠ x := by intro h; exact hi (h.symm ▸ hxu)
    have hp := mul_le_mul hz1 hi1 (hv i) (by norm_num : (0 : ℝ) ≤ 51 / 100)
    have hprod : v z * v i < sqnorm v / n := by nlinarith
    exact low_product_not_adj hG he hu hzx hix hprod hzi
  have hleaf : ∀ z ∉ highSet v, ∀ i, G.Adj z i → i = x := by
    intro z hz i hzi
    by_contra hix
    have hzx : z ≠ x := by intro h; exact hz (h.symm ▸ hxu)
    have hp := mul_le_mul_of_nonneg_left (hv1 i) (hv z)
    have hz0 := hsmall z hz
    have hprod : v z * v i < sqnorm v / n := by nlinarith
    exact low_product_not_adj hG he hu hzx hix hprod hzi
  refine ⟨hxu, ?_⟩
  intro i j
  constructor
  · intro hij
    refine ⟨hij.ne, ?_⟩
    by_cases hix : i = x
    · exact Or.inr (Or.inl hix)
    by_cases hjx : j = x
    · exact Or.inr (Or.inr hjx)
    left
    constructor
    · by_contra hi
      exact hjx (hleaf i hi j hij)
    · by_contra hj
      exact hix (hleaf j hj i hij.symm)
  · rintro ⟨hij, hU | hix | hjx⟩
    · exact hcl i hU.1 j hU.2 hij
    · subst i
      exact (hu j hij.symm).symm
    · subst j
      exact hu i hij

end TaitTobin.Irregularity.Fresh
end

section

open scoped Classical
namespace TaitTobin.Irregularity.Fresh

lemma pineapple_iso_of_shape {n : ℕ} (G : SimpleGraph (Fin n)) (U : Finset (Fin n))
    (x : Fin n) (hx : x ∈ U)
    (hshape : ∀ i j, G.Adj i j ↔ i ≠ j ∧ ((i ∈ U ∧ j ∈ U) ∨ i = x ∨ j = x)) :
    ∃ p q : ℕ, p + q = n ∧ Nonempty (G ≃g pineapple p q) := by
  let S : Set (Fin n) := ↑U
  let p := Fintype.card S
  let q := Fintype.card (Sᶜ : Set (Fin n))
  have hp : 0 < p := Fintype.card_pos_iff.mpr ⟨⟨x, hx⟩⟩
  let e0 : S ≃ Fin p := Fintype.equivFin S
  let eU : S ≃ Fin p := e0.trans (Equiv.swap (e0 ⟨x, hx⟩) ⟨0, hp⟩)
  let eV : (Sᶜ : Set (Fin n)) ≃ Fin q := Fintype.equivFin _
  let e : Fin n ≃ Fin (p + q) := (Equiv.Set.sumCompl S).symm.trans
    ((Equiv.sumCongr eU eV).trans finSumFinEquiv)
  have he_mem (i : Fin n) : (e i : ℕ) < p ↔ i ∈ U := by
    by_cases hi : i ∈ U
    · have hiS : i ∈ S := hi
      simp [e, Equiv.Set.sumCompl_symm_apply_of_mem hiS, hi, Fin.is_lt]
    · have hiS : i ∉ S := hi
      simp [e, Equiv.Set.sumCompl_symm_apply_of_notMem hiS, hi]
  have hex : (e x : ℕ) = 0 := by
    have hxS : x ∈ S := hx
    simp [e, Equiv.Set.sumCompl_symm_apply_of_mem hxS, eU]
  have he_zero (i : Fin n) : (e i : ℕ) = 0 ↔ i = x := by
    constructor
    · intro hi
      apply e.injective
      apply Fin.ext
      exact hi.trans hex.symm
    · rintro rfl
      exact hex
  have he_ge (i : Fin n) : p ≤ (e i : ℕ) ↔ i ∉ U := by
    rw [← not_lt, he_mem]
  have hc : p + q = n := by
    have hh := Fintype.card_congr e
    simpa only [Fintype.card_fin] using hh.symm
  refine ⟨p, q, hc, ⟨{ toEquiv := e, map_rel_iff' := ?_ }⟩⟩
  intro i j
  rw [hshape]
  change (e i ≠ e j ∧ (((e i : ℕ) < p ∧ (e j : ℕ) < p) ∨
    (0 < p ∧ (e i : ℕ) = 0 ∧ p ≤ (e j : ℕ)) ∨
    (0 < p ∧ (e j : ℕ) = 0 ∧ p ≤ (e i : ℕ)))) ↔ _
  rw [e.injective.ne_iff, he_mem, he_mem, he_zero, he_zero, he_ge, he_ge]
  have hix : i = x → i ∈ U := fun h => h ▸ hx
  have hjx : j = x → j ∈ U := fun h => h ▸ hx
  tauto

end TaitTobin.Irregularity.Fresh
end

section

open WangKangXue.SpectralTuran
namespace TaitTobin.Irregularity.Fresh

theorem native_theorem_21 : ∃ N : ℕ, ∀ n ≥ N, ∀ G : SimpleGraph (Fin n), IsIrregMax G →
    ∃ p q : ℕ, p + q = n ∧ Nonempty (G ≃g pineapple p q) := by
  classical
  refine ⟨100000000, ?_⟩
  intro n hn G hG
  obtain ⟨v, hv, hv1, ⟨x, hx⟩, he⟩ := exists_positive_top_vector G hG.1 (by simpa using (show 0 < n by omega))
  have hu := universal_max_vertex hG hv hv1 he hx
  obtain ⟨hxU, hshape⟩ := extremal_shape hn G hG v x (fun i => (hv i).le) hv1 hx hu he
  exact pineapple_iso_of_shape G (highSet v) x hxU hshape

end TaitTobin.Irregularity.Fresh
end

open TaitTobin.Irregularity

theorem solution : ∃ N : ℕ, ∀ n ≥ N, ∀ G : SimpleGraph (Fin n), IsIrregMax G →
    ∃ p q : ℕ, p + q = n ∧ Nonempty (G ≃g pineapple p q)  := by
  exact Fresh.native_theorem_21
