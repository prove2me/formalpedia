-- Prove2me | solution 1 for Polyhedral.lp_strong_duality
-- status  : ACCEPTED   (prove)
-- author  : @Hartmann_Psi
-- created : 2026-09-27T23:26:38.862713+00:00
-- url     : https://prove2.me/submissions/8593581e-318f-4988-8df2-1179a37b0e2f

import Mathlib

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

namespace FGCone

/-- Weyl's theorem for an arbitrary finite index type. -/
theorem isClosed_coneSpan_index {m : ℕ} {ι : Type*} [Fintype ι] (v : ι → (Fin m → ℝ)) :
    IsClosed {z : Fin m → ℝ | ∃ y : ι → ℝ, (∀ j, 0 ≤ y j) ∧ ∑ j, y j • v j = z} := by
  classical
  obtain ⟨e⟩ : Nonempty (ι ≃ Fin (Fintype.card ι)) := ⟨Fintype.equivFin ι⟩
  have hset : {z : Fin m → ℝ | ∃ y : ι → ℝ, (∀ j, 0 ≤ y j) ∧ ∑ j, y j • v j = z}
      = {z : Fin m → ℝ | ∃ y : Fin (Fintype.card ι) → ℝ, (∀ j, 0 ≤ y j) ∧
          ∑ j, y j • v (e.symm j) = z} := by
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨fun j => y (e.symm j), fun j => hy _, ?_⟩
      exact Fintype.sum_equiv e.symm _ _ (fun j => rfl)
    · rintro ⟨y, hy, rfl⟩
      refine ⟨fun j => y (e j), fun j => hy _, ?_⟩
      refine Fintype.sum_equiv e _ _ (fun j => ?_)
      simp
  rw [hset]
  exact isClosed_coneSpan _

end FGCone

namespace LPBasic

variable {m n : ℕ}

/-- The augmented column `(W_{·j}, q_j) ∈ ℝ^{1+m}` with the cost in the leading coordinate. -/
noncomputable def augCol (W : Matrix (Fin m) (Fin n) ℝ) (q : Fin n → ℝ) (j : Fin n) :
    Fin (m + 1) → ℝ :=
  Fin.cons (q j) (fun i => W i j)

lemma sum_augCol (W : Matrix (Fin m) (Fin n) ℝ) (q : Fin n → ℝ) (y : Fin n → ℝ) :
    ∑ j, y j • augCol W q j = Fin.cons (dotProduct q y) (Matrix.mulVec W y) := by
  funext i
  induction i using Fin.cases with
  | zero =>
      simp only [Finset.sum_apply, Pi.smul_apply, augCol, Fin.cons_zero, smul_eq_mul,
        dotProduct]
      exact Finset.sum_congr rfl (fun j _ => by ring)
  | succ i =>
      simp only [Finset.sum_apply, Pi.smul_apply, augCol, Fin.cons_succ, smul_eq_mul,
        Matrix.mulVec, dotProduct]
      exact Finset.sum_congr rfl (fun j _ => by ring)

/-- **Attainment for linear programs in standard form.** If the feasible set is nonempty and
the objective is bounded below on it, the minimum is attained. -/
theorem lp_min_attained (W : Matrix (Fin m) (Fin n) ℝ) (q : Fin n → ℝ) (d : Fin m → ℝ)
    (hfeas : ∃ y : Fin n → ℝ, (∀ j, 0 ≤ y j) ∧ Matrix.mulVec W y = d)
    (hbdd : ∃ beta : ℝ, ∀ y : Fin n → ℝ, (∀ j, 0 ≤ y j) → Matrix.mulVec W y = d →
      beta ≤ dotProduct q y) :
    ∃ y0 : Fin n → ℝ, (∀ j, 0 ≤ y0 j) ∧ Matrix.mulVec W y0 = d ∧
      ∀ y : Fin n → ℝ, (∀ j, 0 ≤ y j) → Matrix.mulVec W y = d →
        dotProduct q y0 ≤ dotProduct q y := by
  classical
  set S : Set ℝ := {r : ℝ | ∃ y : Fin n → ℝ, (∀ j, 0 ≤ y j) ∧ Matrix.mulVec W y = d ∧
    dotProduct q y = r} with hS
  have hSeq : S = (fun r : ℝ => Fin.cons r d) ⁻¹'
      {z : Fin (m + 1) → ℝ | ∃ y : Fin n → ℝ, (∀ j, 0 ≤ y j) ∧ ∑ j, y j • augCol W q j = z} := by
    ext r
    constructor
    · rintro ⟨y, hy, hWy, rfl⟩
      exact ⟨y, hy, by rw [sum_augCol, hWy]⟩
    · rintro ⟨y, hy, hz⟩
      rw [sum_augCol] at hz
      refine ⟨y, hy, ?_, ?_⟩
      · funext i
        have := congrArg (fun f => f i.succ) hz
        simpa using this
      · have := congrArg (fun f => f 0) hz
        simpa using this
  have hcont : Continuous (fun r : ℝ => (Fin.cons r d : Fin (m + 1) → ℝ)) := by
    refine continuous_pi (fun i => ?_)
    induction i using Fin.cases with
    | zero =>
        have he : (fun r : ℝ => (Fin.cons r d : Fin (m + 1) → ℝ) 0) = fun r : ℝ => r := by
          funext r; simp
        rw [he]; exact continuous_id
    | succ i => simpa using continuous_const
  have hSclosed : IsClosed S := by
    rw [hSeq]
    exact (FGCone.isClosed_coneSpan _).preimage hcont
  have hSne : S.Nonempty := by
    obtain ⟨y, hy, hWy⟩ := hfeas
    exact ⟨dotProduct q y, y, hy, hWy, rfl⟩
  have hSbdd : BddBelow S := by
    obtain ⟨beta, hbeta⟩ := hbdd
    refine ⟨beta, ?_⟩
    rintro r ⟨y, hy, hWy, rfl⟩
    exact hbeta y hy hWy
  obtain ⟨hmem, hlb⟩ := hSclosed.isLeast_csInf hSne hSbdd
  obtain ⟨y0, hy0, hWy0, hval⟩ := hmem
  refine ⟨y0, hy0, hWy0, ?_⟩
  intro y hy hWy
  rw [hval]
  exact hlb ⟨y, hy, hWy, rfl⟩

end LPBasic

namespace FGCone

/-- Every continuous linear functional on `Fin m → ℝ` is minus a dot product with the
vector of its values on the standard basis. -/
lemma frepr {m : ℕ} (f : (Fin m → ℝ) →L[ℝ] ℝ) (z : Fin m → ℝ) :
    f z = - dotProduct (fun i => - f (Pi.single i 1)) z := by
  have hz : z = ∑ i, z i • (Pi.single i (1:ℝ)) := by
    funext k
    simp [Finset.sum_apply, Pi.single_apply]
  calc f z = f (∑ i, z i • (Pi.single i (1:ℝ))) := by rw [← hz]
    _ = ∑ i, z i * f (Pi.single i (1:ℝ)) := by
        rw [map_sum]; exact Finset.sum_congr rfl (fun i _ => by rw [map_smul, smul_eq_mul])
    _ = - dotProduct (fun i => - f (Pi.single i 1)) z := by
        rw [dotProduct, ← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl (fun i _ => by ring)

end FGCone

namespace FGCone

variable {m : ℕ} {ι : Type*} [Fintype ι]

/-- The cone generated by a finite family of vectors. -/
def coneSpan (v : ι → (Fin m → ℝ)) : Set (Fin m → ℝ) :=
  {z | ∃ y : ι → ℝ, (∀ j, 0 ≤ y j) ∧ ∑ j, y j • v j = z}

lemma isClosed_coneSpan' (v : ι → (Fin m → ℝ)) : IsClosed (coneSpan v) :=
  isClosed_coneSpan_index v

lemma convex_coneSpan (v : ι → (Fin m → ℝ)) : Convex ℝ (coneSpan v) := by
  rintro z1 ⟨y1, hy1, rfl⟩ z2 ⟨y2, hy2, rfl⟩ a b ha hb _
  refine ⟨a • y1 + b • y2, fun j => by
    have := mul_nonneg ha (hy1 j); have := mul_nonneg hb (hy2 j)
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; linarith, ?_⟩
  rw [Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, smul_smul]
  module

lemma zero_mem_coneSpan (v : ι → (Fin m → ℝ)) : (0 : Fin m → ℝ) ∈ coneSpan v :=
  ⟨0, fun _ => le_rfl, by simp⟩

lemma smul_mem_coneSpan (v : ι → (Fin m → ℝ)) {z : Fin m → ℝ} (hz : z ∈ coneSpan v)
    {t : ℝ} (ht : 0 ≤ t) : t • z ∈ coneSpan v := by
  obtain ⟨y, hy, rfl⟩ := hz
  refine ⟨t • y, fun j => mul_nonneg ht (hy j), ?_⟩
  rw [Finset.smul_sum]
  exact Finset.sum_congr rfl (fun j _ => by simp [smul_smul])

lemma gen_mem_coneSpan [DecidableEq ι] (v : ι → (Fin m → ℝ)) (j : ι) : v j ∈ coneSpan v := by
  refine ⟨Pi.single j 1, fun k => ?_, ?_⟩
  · by_cases h : k = j <;> simp [Pi.single_apply, h]
  · simp [Pi.single_apply, Finset.sum_ite_eq']

/-- **Separation form of Farkas' lemma.** A vector outside the cone generated by a finite
family admits a linear functional nonnegative on the family and negative at the vector. -/
theorem exists_separating_of_notMem_coneSpan [DecidableEq ι] (v : ι → (Fin m → ℝ))
    {b : Fin m → ℝ} (hb : b ∉ coneSpan v) :
    ∃ w : Fin m → ℝ, (∀ j, 0 ≤ dotProduct w (v j)) ∧ dotProduct w b < 0 := by
  obtain ⟨f, u, hfs, hfb⟩ :=
    geometric_hahn_banach_closed_point (convex_coneSpan v) (isClosed_coneSpan' v) hb
  have hu : 0 < u := by
    have h := hfs 0 (zero_mem_coneSpan v)
    simpa using h
  have hcone_le : ∀ z ∈ coneSpan v, f z ≤ 0 := by
    intro z hz
    by_contra hpos
    push_neg at hpos
    have ht : (0:ℝ) ≤ (u + 1) / f z := by positivity
    have h := hfs _ (smul_mem_coneSpan v hz ht)
    rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ (ne_of_gt hpos)] at h
    linarith
  refine ⟨fun i => - f (Pi.single i 1), ?_, ?_⟩
  · intro j
    have hrepr := frepr f (v j)
    have := hcone_le _ (gen_mem_coneSpan v j)
    rw [hrepr] at this
    linarith
  · have hrepr := frepr f b
    rw [hrepr] at hfb
    linarith

end FGCone

namespace LPBasic

/-- **Gale's theorem of the alternative.** If `B π ≤ c` has no solution then there is
`w ≥ 0` with `Bᵀ w = 0` and `wᵀ c < 0`. -/
theorem gale_alternative {r k : ℕ} (B : Matrix (Fin r) (Fin k) ℝ) (c : Fin r → ℝ)
    (hno : ¬ ∃ pi : Fin k → ℝ, ∀ i, Matrix.mulVec B pi i ≤ c i) :
    ∃ w : Fin r → ℝ, (∀ i, 0 ≤ w i) ∧ Matrix.mulVec Bᵀ w = 0 ∧ dotProduct w c < 0 := by
  classical
  set v : (Fin k ⊕ Fin k) ⊕ Fin r → (Fin r → ℝ) := fun t =>
    match t with
    | Sum.inl (Sum.inl j) => fun i => B i j
    | Sum.inl (Sum.inr j) => fun i => -(B i j)
    | Sum.inr i => Pi.single i 1 with hv
  have hnotmem : c ∉ FGCone.coneSpan v := by
    rintro ⟨y, hy, hsum⟩
    refine hno ⟨fun j => y (Sum.inl (Sum.inl j)) - y (Sum.inl (Sum.inr j)), ?_⟩
    intro i
    have hc : c i = Matrix.mulVec B (fun j => y (Sum.inl (Sum.inl j)) -
        y (Sum.inl (Sum.inr j))) i + y (Sum.inr i) := by
      rw [← hsum]
      rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
      simp only [Finset.sum_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hv,
        Matrix.mulVec, dotProduct]
      have h3 : ∑ x, y (Sum.inr x) * (Pi.single x (1:ℝ) : Fin r → ℝ) i = y (Sum.inr i) := by
        simp [Pi.single_apply, Finset.sum_ite_eq']
      rw [h3]
      congr 1
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun x _ => by ring)
    have := hy (Sum.inr i)
    linarith [hc]
  obtain ⟨w, hwnn, hwc⟩ := FGCone.exists_separating_of_notMem_coneSpan v hnotmem
  refine ⟨w, ?_, ?_, hwc⟩
  · intro i
    have h := hwnn (Sum.inr i)
    simpa [hv, dotProduct, Pi.single_apply] using h
  · funext j
    have h1 := hwnn (Sum.inl (Sum.inl j))
    have h2 := hwnn (Sum.inl (Sum.inr j))
    simp only [hv, dotProduct] at h1 h2
    have h2' : ∑ i, w i * B i j ≤ 0 := by
      have : ∑ i, w i * -(B i j) = -∑ i, w i * B i j := by
        rw [← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl (fun i _ => by ring)
      rw [this] at h2; linarith
    have : ∑ i, w i * B i j = 0 := le_antisymm h2' h1
    simpa [Matrix.mulVec, dotProduct, Matrix.transpose_apply, mul_comm] using this

end LPBasic

namespace LPBasic

/-- **Strong duality with complementary slackness for a linear program in standard form.**
If `u0` is optimal for `min dᵀu` subject to `M u = g, u ≥ 0`, then there is a dual vector `π`
with `Mᵀπ ≤ d`, equal objective value, and complementary slackness. -/
theorem lp_strong_duality {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ) (dv : Fin n → ℝ)
    (g : Fin m → ℝ) (u0 : Fin n → ℝ) (hu0 : ∀ j, 0 ≤ u0 j) (hMu0 : Matrix.mulVec M u0 = g)
    (hopt : ∀ u : Fin n → ℝ, (∀ j, 0 ≤ u j) → Matrix.mulVec M u = g →
      dotProduct dv u0 ≤ dotProduct dv u) :
    ∃ pi : Fin m → ℝ, (∀ j, Matrix.mulVec Mᵀ pi j ≤ dv j) ∧
      dotProduct g pi = dotProduct dv u0 ∧
      ∀ j, u0 j * (dv j - Matrix.mulVec Mᵀ pi j) = 0 := by
  classical
  set val : ℝ := dotProduct dv u0 with hvaldef
  set B : Matrix (Fin (n + 1)) (Fin m) ℝ :=
    Matrix.of (Fin.cons (fun j => -g j) (fun i' j => M j i')) with hB
  set cc : Fin (n + 1) → ℝ := Fin.cons (-val) dv with hcc
  have hB0 : ∀ j, B 0 j = -g j := by intro j; simp [hB]
  have hBS : ∀ (i' : Fin n) (j), B i'.succ j = M j i' := by intro i' j; simp [hB]
  have hBrow0 : ∀ pi : Fin m → ℝ, Matrix.mulVec B pi 0 = - dotProduct g pi := by
    intro pi
    simp only [Matrix.mulVec, dotProduct, hB0]
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  have hBrowS : ∀ (pi : Fin m → ℝ) (i' : Fin n),
      Matrix.mulVec B pi i'.succ = Matrix.mulVec Mᵀ pi i' := by
    intro pi i'
    simp only [Matrix.mulVec, dotProduct, hBS, Matrix.transpose_apply]
  have hsol : ∃ pi : Fin m → ℝ, ∀ i, Matrix.mulVec B pi i ≤ cc i := by
    by_contra hno
    obtain ⟨w, hwnn, hwB, hwc⟩ := gale_alternative B cc hno
    set t : ℝ := w 0 with htdef
    set u : Fin n → ℝ := fun i' => w i'.succ with hudef
    have ht : 0 ≤ t := hwnn 0
    have hu : ∀ i', 0 ≤ u i' := fun i' => hwnn _
    have hkey : ∀ j, Matrix.mulVec M u j = t * g j := by
      intro j
      have h := congrArg (fun f => f j) hwB
      simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Pi.zero_apply] at h
      rw [Fin.sum_univ_succ] at h
      rw [hB0 j] at h
      have h2 : ∑ i' : Fin n, B i'.succ j * w i'.succ = ∑ i' : Fin n, M j i' * u i' :=
        Finset.sum_congr rfl (fun i' _ => by rw [hBS])
      rw [h2] at h
      simp only [Matrix.mulVec, dotProduct]
      linarith
    have hobj : dotProduct dv u - t * val < 0 := by
      have h := hwc
      simp only [dotProduct] at h
      rw [Fin.sum_univ_succ] at h
      have h2 : ∑ i' : Fin n, w i'.succ * cc i'.succ = ∑ i' : Fin n, dv i' * u i' := by
        refine Finset.sum_congr rfl (fun i' _ => ?_)
        simp only [hcc, Fin.cons_succ, hudef]
        ring
      rw [h2] at h
      have h3 : cc 0 = -val := by simp [hcc]
      rw [h3] at h
      simp only [dotProduct]
      linarith
    rcases eq_or_lt_of_le ht with htz | htp
    · have hMu : Matrix.mulVec M u = 0 := by
        funext j; rw [hkey j, ← htz]; simp
      have h1 : Matrix.mulVec M (u0 + u) = g := by
        rw [Matrix.mulVec_add, hMu0, hMu, add_zero]
      have h2 : ∀ j, 0 ≤ (u0 + u) j := by
        intro j; have := hu0 j; have := hu j; simp only [Pi.add_apply]; linarith
      have hstep := hopt _ h2 h1
      have h4 : dotProduct dv (u0 + u) = dotProduct dv u0 + dotProduct dv u := by
        simp only [dotProduct, Pi.add_apply]
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl (fun j _ => by ring)
      rw [h4] at hstep
      have : dotProduct dv u < 0 := by rw [← htz] at hobj; linarith
      linarith [hstep]
    · set ub : Fin n → ℝ := fun j => u j / t with hubdef
      have hubnn : ∀ j, 0 ≤ ub j := fun j => div_nonneg (hu j) htp.le
      have hubM : Matrix.mulVec M ub = g := by
        funext j
        have : Matrix.mulVec M ub j = (Matrix.mulVec M u j) / t := by
          simp only [Matrix.mulVec, dotProduct, hubdef]
          rw [Finset.sum_div]
          exact Finset.sum_congr rfl (fun i _ => by ring)
        rw [this, hkey j]
        field_simp
      have hstep := hopt _ hubnn hubM
      have h5 : dotProduct dv ub = (dotProduct dv u) / t := by
        simp only [dotProduct, hubdef]
        rw [Finset.sum_div]
        exact Finset.sum_congr rfl (fun i _ => by ring)
      rw [h5] at hstep
      rw [le_div_iff₀ htp] at hstep
      have hcomm : val * t = t * val := mul_comm _ _
      linarith
  obtain ⟨pi, hpi⟩ := hsol
  have hfeas : ∀ j, Matrix.mulVec Mᵀ pi j ≤ dv j := by
    intro j
    have h := hpi j.succ
    rw [hBrowS] at h
    have : cc j.succ = dv j := by simp [hcc]
    rwa [this] at h
  have hge : val ≤ dotProduct g pi := by
    have h := hpi 0
    rw [hBrow0] at h
    have h0 : cc 0 = -val := by simp [hcc]
    rw [h0] at h
    linarith
  have hweak : dotProduct g pi = dotProduct (Matrix.mulVec Mᵀ pi) u0 := by
    rw [← hMu0]
    simp only [dotProduct, Matrix.mulVec, Matrix.transpose_apply]
    have L : ∑ i, (∑ j, M i j * u0 j) * pi i = ∑ i, ∑ j, M i j * u0 j * pi i :=
      Finset.sum_congr rfl (fun i _ => by rw [Finset.sum_mul])
    have R : ∑ j, (∑ i, M i j * pi i) * u0 j = ∑ j, ∑ i, M i j * pi i * u0 j :=
      Finset.sum_congr rfl (fun j _ => by rw [Finset.sum_mul])
    rw [L, R, Finset.sum_comm]
    exact Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun i _ => by ring))
  have hle : dotProduct g pi ≤ val := by
    rw [hweak, hvaldef]
    simp only [dotProduct]
    exact Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_right (hfeas j) (hu0 j))
  have heq : dotProduct g pi = val := le_antisymm hle hge
  have hcssum : ∑ j, u0 j * (dv j - Matrix.mulVec Mᵀ pi j) = 0 := by
    have hsplit : ∑ j, u0 j * (dv j - Matrix.mulVec Mᵀ pi j)
        = dotProduct dv u0 - dotProduct (Matrix.mulVec Mᵀ pi) u0 := by
      simp only [dotProduct]
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun j _ => by ring)
    rw [hsplit, ← hweak, heq, hvaldef]
    ring
  refine ⟨pi, hfeas, heq.trans hvaldef, ?_⟩
  intro j
  have hnn : ∀ k ∈ (Finset.univ : Finset (Fin n)),
      0 ≤ u0 k * (dv k - Matrix.mulVec Mᵀ pi k) := by
    intro k _
    have := hfeas k
    exact mul_nonneg (hu0 k) (by linarith)
  exact (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hcssum j (Finset.mem_univ j)

end LPBasic

/-- Top-level entry point: strong duality with complementary slackness. -/
theorem solution {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ) (d : Fin n → ℝ)
    (g : Fin m → ℝ) (u0 : Fin n → ℝ) (hu0 : ∀ j, 0 ≤ u0 j) (hMu0 : M.mulVec u0 = g)
    (hopt : ∀ u : Fin n → ℝ, (∀ j, 0 ≤ u j) → M.mulVec u = g →
      dotProduct d u0 ≤ dotProduct d u) :
    ∃ p : Fin m → ℝ, (∀ j, Mᵀ.mulVec p j ≤ d j) ∧ dotProduct g p = dotProduct d u0 ∧
      ∀ j, u0 j * (d j - Mᵀ.mulVec p j) = 0 :=
  LPBasic.lp_strong_duality M d g u0 hu0 hMu0 hopt
