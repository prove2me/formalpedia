-- Prove2me | solution 1 for StochasticProg.Recourse.thm5a_K2_closed_convex
-- status  : ACCEPTED   (prove)
-- author  : @Hartmann_Psi
-- created : 2026-09-27T23:04:22.258979+00:00
-- url     : https://prove2.me/submissions/fa4f445b-bbd5-4c8c-9783-b3aefa24656c

import Mathlib
import Definitions.Def_StochasticProg_Recourse_Instance


open scoped BigOperators
open Matrix

namespace FGCone

variable {m n : ℕ}

/-- The conic hull of the columns of `W`, i.e. the image of the nonnegative orthant
under `y ↦ W y`. -/
def coneOf (W : Matrix (Fin m) (Fin n) ℝ) : Set (Fin m → ℝ) :=
  {z | ∃ y : Fin n → ℝ, (∀ j, 0 ≤ y j) ∧ W.mulVec y = z}

/-- `W.mulVec y` written as the nonnegative combination of the columns of `W`. -/
lemma mulVec_eq_sum (W : Matrix (Fin m) (Fin n) ℝ) (y : Fin n → ℝ) :
    W.mulVec y = ∑ j, y j • (fun i => W i j) := by
  funext i
  simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]

/-- Conic Carathéodory: any nonnegative combination of a finite family of vectors can be
rewritten as a nonnegative combination supported on a linearly independent subfamily. -/
lemma exists_linearIndepOn_repr (v : Fin n → (Fin m → ℝ)) :
    ∀ (N : ℕ) (y : Fin n → ℝ), (∀ j, 0 ≤ y j) →
      {j | y j ≠ 0}.toFinset.card ≤ N →
      ∃ y' : Fin n → ℝ, (∀ j, 0 ≤ y' j) ∧ (∑ j, y' j • v j) = ∑ j, y j • v j ∧
        LinearIndepOn ℝ v {j | y' j ≠ 0} := by
  classical
  intro N
  induction N with
  | zero =>
      intro y hy hcard
      refine ⟨y, hy, rfl, ?_⟩
      have h0 : {j | y j ≠ 0}.toFinset = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hcard)
      have : {j : Fin n | y j ≠ 0} = ∅ := by
        ext j; constructor
        · intro hj
          have : j ∈ {j | y j ≠ 0}.toFinset := by simpa using hj
          simp [h0] at this
        · intro hj; exact absurd hj (Set.notMem_empty j)
      rw [this]
      exact linearIndepOn_empty ℝ v
  | succ N ih =>
      intro y hy hcard
      by_cases hindep : LinearIndepOn ℝ v {j | y j ≠ 0}
      · exact ⟨y, hy, rfl, hindep⟩
      · -- extract a nontrivial dependence supported on the support of `y`
        set S : Finset (Fin n) := {j | y j ≠ 0}.toFinset with hS
        have hSset : (S : Set (Fin n)) = {j | y j ≠ 0} := by
          simp [hS]
        have hdep : ¬ LinearIndepOn ℝ v (S : Set (Fin n)) := by rwa [hSset]
        obtain ⟨f, hf0, j1, hj1S, hj1⟩ := not_linearIndepOn_finset_iff.mp hdep
        -- make `f` supported exactly on `S`
        set g : Fin n → ℝ := fun j => if j ∈ S then f j else 0 with hg
        have hgsum : ∑ j, g j • v j = 0 := by
          have e1 : ∑ j, g j • v j = ∑ j ∈ S, g j • v j :=
            (Finset.sum_subset (Finset.subset_univ S)
              (fun j _ hj => by simp [hg, hj])).symm
          rw [e1, ← hf0]
          exact Finset.sum_congr rfl (fun j hj => by simp [hg, hj])
        have hgsupp : ∀ j, g j ≠ 0 → j ∈ S := by
          intro j hj; by_contra h; simp [hg, h] at hj
        have hgne : ∃ j, g j ≠ 0 := ⟨j1, by simpa [hg, hj1S] using hj1⟩
        -- normalise so that some coordinate is positive
        obtain ⟨mu, hmusum, hmusupp, j0, hj0pos⟩ :
            ∃ mu : Fin n → ℝ, (∑ j, mu j • v j = 0) ∧ (∀ j, mu j ≠ 0 → j ∈ S) ∧
              ∃ j0, 0 < mu j0 := by
          obtain ⟨j, hj⟩ := hgne
          rcases lt_or_gt_of_ne hj with hneg | hpos
          · refine ⟨fun k => -g k, ?_, ?_, j, by linarith⟩
            · simp only [neg_smul, Finset.sum_neg_distrib, hgsum, neg_zero]
            · intro k hk; exact hgsupp k (by simpa using fun h => hk (by simp [h]))
          · exact ⟨g, hgsum, hgsupp, j, hpos⟩
        -- the blocking ratio
        set P : Finset (Fin n) := Finset.univ.filter (fun j => 0 < mu j) with hP
        have hPne : P.Nonempty := ⟨j0, by simp [hP, hj0pos]⟩
        obtain ⟨jm, hjmP, hjmmin⟩ := P.exists_min_image (fun j => y j / mu j) hPne
        set t : ℝ := y jm / mu jm with ht
        have hmujm : 0 < mu jm := by simpa [hP] using hjmP
        have ht0 : 0 ≤ t := div_nonneg (hy jm) hmujm.le
        set y' : Fin n → ℝ := fun j => y j - t * mu j with hy'
        have hy'nonneg : ∀ j, 0 ≤ y' j := by
          intro j
          by_cases hmj : 0 < mu j
          · have hjP : j ∈ P := by simp [hP, hmj]
            have := hjmmin j hjP
            -- t ≤ y j / mu j
            have h2 : t * mu j ≤ (y j / mu j) * mu j :=
              mul_le_mul_of_nonneg_right this hmj.le
            rw [div_mul_cancel₀ _ (ne_of_gt hmj)] at h2
            simp only [hy']; linarith
          · have hmj' : mu j ≤ 0 := le_of_not_gt hmj
            have : t * mu j ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ht0 hmj'
            simp only [hy']; linarith [hy j]
        have hy'jm : y' jm = 0 := by
          simp only [hy', ht, div_mul_cancel₀ _ (ne_of_gt hmujm), sub_self]
        have hy'sum : ∑ j, y' j • v j = ∑ j, y j • v j := by
          have : ∑ j, y' j • v j = (∑ j, y j • v j) - t • ∑ j, mu j • v j := by
            rw [Finset.smul_sum, ← Finset.sum_sub_distrib]
            refine Finset.sum_congr rfl (fun j _ => ?_)
            simp only [hy', smul_smul, sub_smul]
          rw [this, hmusum, smul_zero, sub_zero]
        have hsupp' : {j | y' j ≠ 0}.toFinset ⊆ S.erase jm := by
          intro j hj
          simp only [Set.mem_toFinset, Set.mem_setOf_eq] at hj
          refine Finset.mem_erase.mpr ⟨?_, ?_⟩
          · rintro rfl; exact hj hy'jm
          · by_contra hjS
            have hyj : y j = 0 := by
              by_contra h; exact hjS (by simp [hS, h])
            have hmuj : mu j = 0 := by
              by_contra h; exact hjS (hmusupp j h)
            exact hj (by simp [hy', hyj, hmuj])
        have hcard' : {j | y' j ≠ 0}.toFinset.card ≤ N := by
          have h1 : {j | y' j ≠ 0}.toFinset.card ≤ (S.erase jm).card :=
            Finset.card_le_card hsupp'
          have hjmS : jm ∈ S := by
            have : mu jm ≠ 0 := ne_of_gt hmujm
            exact hmusupp jm this
          have h2 : (S.erase jm).card = S.card - 1 := Finset.card_erase_of_mem hjmS
          have h3 : 1 ≤ S.card := Finset.card_pos.mpr ⟨jm, hjmS⟩
          omega
        obtain ⟨y'', h1, h2, h3⟩ := ih y' hy'nonneg hcard'
        exact ⟨y'', h1, by rw [h2, hy'sum], h3⟩

/-- For a linearly independent subfamily indexed by `S`, the image of the nonnegative
orthant is closed: the map is an injective linear map between finite-dimensional spaces. -/
lemma isClosed_image_of_linearIndepOn (v : Fin n → (Fin m → ℝ)) (S : Finset (Fin n))
    (hS : LinearIndepOn ℝ v (S : Set (Fin n))) :
    IsClosed ((fun w : {x // x ∈ S} → ℝ => ∑ j, w j • v (j : Fin n)) '' {w | ∀ j, 0 ≤ w j}) := by
  classical
  set L : ({x // x ∈ S} → ℝ) →ₗ[ℝ] (Fin m → ℝ) :=
    Fintype.linearCombination ℝ (fun j : {x // x ∈ S} => v (j : Fin n)) with hL
  have hker : LinearMap.ker L = ⊥ := by
    refine LinearMap.ker_eq_bot'.mpr ?_
    intro w hw
    have hw' : ∑ j : {x // x ∈ S}, w j • v (j : Fin n) = 0 := hw
    set f : Fin n → ℝ := fun i => if h : i ∈ S then w ⟨i, h⟩ else 0 with hf
    have hfS : ∑ i ∈ S, f i • v i = 0 := by
      rw [← Finset.sum_attach S (fun i => f i • v i)]
      rw [← hw']
      rw [Finset.univ_eq_attach]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      simp [hf, j.2]
    have := linearIndepOn_finset_iff.mp hS f hfS
    funext j
    have hj := this (j : Fin n) j.2
    simpa [hf, j.2] using hj
  have hcl : IsClosed {w : {x // x ∈ S} → ℝ | ∀ j, 0 ≤ w j} := by
    rw [Set.setOf_forall]
    exact isClosed_iInter fun j => isClosed_le continuous_const (continuous_apply j)
  have heq : (fun w : {x // x ∈ S} → ℝ => ∑ j, w j • v (j : Fin n)) = ⇑L := by
    funext w
    simp only [hL, Fintype.linearCombination_apply]
  rw [heq]
  exact (LinearMap.isClosedEmbedding_of_injective (f := L) hker).isClosedMap _ hcl

/-- **Weyl's theorem**: the conic hull of finitely many vectors is closed. -/
theorem isClosed_coneSpan (v : Fin n → (Fin m → ℝ)) :
    IsClosed {z : Fin m → ℝ | ∃ y : Fin n → ℝ, (∀ j, 0 ≤ y j) ∧ ∑ j, y j • v j = z} := by
  classical
  have key : {z : Fin m → ℝ | ∃ y : Fin n → ℝ, (∀ j, 0 ≤ y j) ∧ ∑ j, y j • v j = z}
      = ⋃ S : {S : Finset (Fin n) // LinearIndepOn ℝ v (S : Set (Fin n))},
          (fun w : {x // x ∈ S.1} → ℝ => ∑ j, w j • v (j : Fin n)) '' {w | ∀ j, 0 ≤ w j} := by
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨y', hy', hsum, hindep⟩ :=
        exists_linearIndepOn_repr v {j | y j ≠ 0}.toFinset.card y hy le_rfl
      have hindep' : LinearIndepOn ℝ v (({j | y' j ≠ 0}.toFinset : Finset (Fin n)) : Set (Fin n)) := by
        simpa [Set.coe_toFinset] using hindep
      refine Set.mem_iUnion.mpr ⟨⟨{j | y' j ≠ 0}.toFinset, hindep'⟩, ?_⟩
      refine ⟨fun j => y' (j : Fin n), fun j => hy' _, ?_⟩
      show ∑ j : {x // x ∈ {j | y' j ≠ 0}.toFinset}, y' (j : Fin n) • v (j : Fin n)
        = ∑ j, y j • v j
      rw [Finset.univ_eq_attach,
        Finset.sum_attach {j | y' j ≠ 0}.toFinset (fun i => y' i • v i), ← hsum]
      refine Finset.sum_subset (Finset.subset_univ _) ?_
      intro j _ hj
      have hzero : y' j = 0 := by by_contra h; exact hj (by simp [h])
      simp [hzero]
    · intro hz
      obtain ⟨S, hmem⟩ := Set.mem_iUnion.mp hz
      obtain ⟨w, hw, rfl⟩ := hmem
      set y : Fin n → ℝ := fun j => if h : j ∈ S.1 then w ⟨j, h⟩ else 0 with hy
      refine ⟨y, ?_, ?_⟩
      · intro j
        by_cases h : j ∈ S.1
        · simpa [hy, h] using hw ⟨j, h⟩
        · simp [hy, h]
      · have e1 : ∑ j, y j • v j = ∑ j ∈ S.1, y j • v j :=
          (Finset.sum_subset (Finset.subset_univ S.1) (fun j _ hj => by simp [hy, hj])).symm
        rw [e1, ← Finset.sum_attach S.1 (fun i => y i • v i)]
        show ∑ j ∈ S.1.attach, y (j : Fin n) • v (j : Fin n)
          = ∑ j : {x // x ∈ S.1}, w j • v (j : Fin n)
        rw [Finset.univ_eq_attach]
        exact Finset.sum_congr rfl (fun j _ => by simp [hy, j.2])
  rw [key]
  exact isClosed_iUnion_of_finite (fun S => isClosed_image_of_linearIndepOn v S.1 S.2)

/-- The image of the nonnegative orthant under `y ↦ W y` is closed. -/
theorem isClosed_coneOf (W : Matrix (Fin m) (Fin n) ℝ) : IsClosed (coneOf W) := by
  have h : coneOf W
      = {z : Fin m → ℝ | ∃ y : Fin n → ℝ, (∀ j, 0 ≤ y j) ∧ ∑ j, y j • (fun i => W i j) = z} := by
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩; exact ⟨y, hy, (mulVec_eq_sum W y).symm⟩
    · rintro ⟨y, hy, rfl⟩; exact ⟨y, hy, mulVec_eq_sum W y⟩
  rw [h]
  exact isClosed_coneSpan _

/-- The image of the nonnegative orthant under `y ↦ W y` is convex. -/
theorem convex_coneOf (W : Matrix (Fin m) (Fin n) ℝ) : Convex ℝ (coneOf W) := by
  rintro z1 ⟨y1, hy1, rfl⟩ z2 ⟨y2, hy2, rfl⟩ a b ha hb _
  refine ⟨a • y1 + b • y2, fun j => ?_, ?_⟩
  · have := mul_nonneg ha (hy1 j)
    have := mul_nonneg hb (hy2 j)
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linarith
  · simp [Matrix.mulVec_add, Matrix.mulVec_smul]

end FGCone

namespace StochasticProg.Recourse

variable {n1 n2 m1 m2 K : ℕ}

/-- The book's aggregation `bookAdd` never produces `⊤` unless one summand does. -/
lemma foldr_bookAdd_ne_top (l : List EReal) :
    l.foldr bookAdd 0 ≠ ⊤ ↔ ∀ a ∈ l, a ≠ ⊤ := by
  induction l with
  | nil => simp
  | cons a l ih =>
      rw [List.foldr_cons]
      by_cases ha : a = ⊤
      · simp [bookAdd, ha]
      · by_cases hr : l.foldr bookAdd 0 = ⊤
        · have hno : ¬ (∀ b ∈ l, b ≠ ⊤) := fun h => (ih.mpr h) hr
          simp [bookAdd, ha, hr, hno]
        · have hval : bookAdd a (l.foldr bookAdd 0) = a + l.foldr bookAdd 0 := by
            simp [bookAdd, ha, hr]
          rw [hval]
          simp only [List.mem_cons, forall_eq_or_imp]
          exact ⟨fun _ => ⟨ha, ih.mp hr⟩, fun _ => EReal.add_ne_top ha hr⟩

/-- `Q(x)` is finite-or-`-∞` exactly when every scenario term is. -/
lemma Q_ne_top_iff (inst : Instance n1 n2 m1 m2 K) (x : Fin n1 → ℝ) :
    Q inst x ≠ ⊤ ↔ ∀ k, ((inst.p k : ℝ) : EReal) * QVal inst x k ≠ ⊤ := by
  rw [Q, foldr_bookAdd_ne_top]
  constructor
  · intro h k
    exact h _ (List.mem_ofFn.mpr ⟨k, rfl⟩)
  · intro h a hmem
    obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hmem
    exact h k

/-- The `k`-th scenario value is `⊤` exactly when the second-stage program is infeasible. -/
lemma QVal_ne_top_iff (inst : Instance n1 n2 m1 m2 K) (x : Fin n1 → ℝ) (k : Fin K) :
    QVal inst x k ≠ ⊤ ↔ ∃ y : Fin n2 → ℝ, (∀ i, 0 ≤ y i) ∧
      Matrix.mulVec inst.W y = inst.h k - Matrix.mulVec (inst.T k) x := by
  constructor
  · intro hne
    by_contra hnone
    push_neg at hnone
    have hempty : {z : EReal | ∃ y : Fin n2 → ℝ, (∀ i, 0 ≤ y i) ∧
        Matrix.mulVec inst.W y = inst.h k - Matrix.mulVec (inst.T k) x ∧
        z = ((dotProduct (inst.q k) y : ℝ) : EReal)} = ∅ := by
      ext z
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨y, hy, hWy, rfl⟩
      exact hnone y hy hWy
    apply hne
    rw [QVal, hempty, sInf_empty]
  · rintro ⟨y, hy, hWy⟩
    have hmem : ((dotProduct (inst.q k) y : ℝ) : EReal) ∈
        {z : EReal | ∃ y : Fin n2 → ℝ, (∀ i, 0 ≤ y i) ∧
          Matrix.mulVec inst.W y = inst.h k - Matrix.mulVec (inst.T k) x ∧
          z = ((dotProduct (inst.q k) y : ℝ) : EReal)} := ⟨y, hy, hWy, rfl⟩
    have hle : QVal inst x k ≤ ((dotProduct (inst.q k) y : ℝ) : EReal) := sInf_le hmem
    exact ne_top_of_le_ne_top (EReal.coe_ne_top _) hle

/-- With `p k ≥ 0`, the scenario term is `⊤` only if the scenario has positive probability
and is infeasible. -/
lemma scenario_term_ne_top_iff (inst : Instance n1 n2 m1 m2 K) (x : Fin n1 → ℝ) (k : Fin K) :
    ((inst.p k : ℝ) : EReal) * QVal inst x k ≠ ⊤ ↔
      (0 < inst.p k → ∃ y : Fin n2 → ℝ, (∀ i, 0 ≤ y i) ∧
        Matrix.mulVec inst.W y = inst.h k - Matrix.mulVec (inst.T k) x) := by
  rw [ne_eq, EReal.mul_eq_top]
  have hnn : ¬ ((inst.p k : ℝ) < 0) := not_lt.mpr (inst.hp_nonneg k)
  simp only [EReal.coe_ne_bot, EReal.coe_ne_top, false_and, false_or, EReal.coe_neg',
    EReal.coe_pos, hnn, not_and]
  exact forall_congr' fun _ => QVal_ne_top_iff inst x k

/-- Chapter 3, Theorem 5(a): `K2` is closed and convex. -/
theorem thm5a_K2_closed_convex (inst : Instance n1 n2 m1 m2 K) :
    IsClosed (K2 inst) ∧ Convex ℝ (K2 inst) := by
  classical
  have hset : K2 inst = ⋂ k : Fin K, {x : Fin n1 → ℝ |
      0 < inst.p k → ∃ y : Fin n2 → ℝ, (∀ i, 0 ≤ y i) ∧
        Matrix.mulVec inst.W y = inst.h k - Matrix.mulVec (inst.T k) x} := by
    ext x
    simp only [K2, Set.mem_setOf_eq, Set.mem_iInter]
    rw [Q_ne_top_iff]
    exact forall_congr' fun k => scenario_term_ne_top_iff inst x k
  have hcont : ∀ k : Fin K,
      Continuous (fun x : Fin n1 → ℝ => inst.h k - Matrix.mulVec (inst.T k) x) := by
    intro k
    have h1 : Continuous (fun x : Fin n1 → ℝ => Matrix.mulVec (inst.T k) x) := by
      refine continuous_pi (fun i => ?_)
      simp only [Matrix.mulVec, dotProduct]
      exact continuous_finset_sum _ (fun j _ => (continuous_apply j).const_mul _)
    exact continuous_const.sub h1
  have hAclosed : ∀ k : Fin K, IsClosed {x : Fin n1 → ℝ |
      0 < inst.p k → ∃ y : Fin n2 → ℝ, (∀ i, 0 ≤ y i) ∧
        Matrix.mulVec inst.W y = inst.h k - Matrix.mulVec (inst.T k) x} := by
    intro k
    by_cases hp : 0 < inst.p k
    · have he : {x : Fin n1 → ℝ |
          0 < inst.p k → ∃ y : Fin n2 → ℝ, (∀ i, 0 ≤ y i) ∧
            Matrix.mulVec inst.W y = inst.h k - Matrix.mulVec (inst.T k) x}
          = (fun x : Fin n1 → ℝ => inst.h k - Matrix.mulVec (inst.T k) x) ⁻¹'
              (FGCone.coneOf inst.W) := by
        ext x
        simp [hp, FGCone.coneOf]
      rw [he]
      exact (FGCone.isClosed_coneOf inst.W).preimage (hcont k)
    · have he : {x : Fin n1 → ℝ |
          0 < inst.p k → ∃ y : Fin n2 → ℝ, (∀ i, 0 ≤ y i) ∧
            Matrix.mulVec inst.W y = inst.h k - Matrix.mulVec (inst.T k) x}
          = Set.univ := by
        ext x; simp [hp]
      rw [he]
      exact isClosed_univ
  have hAconvex : ∀ k : Fin K, Convex ℝ {x : Fin n1 → ℝ |
      0 < inst.p k → ∃ y : Fin n2 → ℝ, (∀ i, 0 ≤ y i) ∧
        Matrix.mulVec inst.W y = inst.h k - Matrix.mulVec (inst.T k) x} := by
    intro k x1 h1 x2 h2 a b ha hb hab hp
    obtain ⟨y1, hy1, e1⟩ := h1 hp
    obtain ⟨y2, hy2, e2⟩ := h2 hp
    refine ⟨a • y1 + b • y2, ?_, ?_⟩
    · intro i
      have t1 := mul_nonneg ha (hy1 i)
      have t2 := mul_nonneg hb (hy2 i)
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      linarith
    · rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, e1, e2]
      funext i
      simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul,
        Matrix.mulVec_add, Matrix.mulVec_smul]
      linear_combination (inst.h k i) * hab
  refine ⟨?_, ?_⟩
  · rw [hset]; exact isClosed_iInter hAclosed
  · rw [hset]; exact convex_iInter hAconvex

end StochasticProg.Recourse

/-- Top-level entry point: Chapter 3, Theorem 5(a). -/
theorem solution {n1 n2 m1 m2 K : ℕ} (inst : StochasticProg.Recourse.Instance n1 n2 m1 m2 K) :
    IsClosed (StochasticProg.Recourse.K2 inst) ∧
      Convex ℝ (StochasticProg.Recourse.K2 inst) :=
  StochasticProg.Recourse.thm5a_K2_closed_convex inst
