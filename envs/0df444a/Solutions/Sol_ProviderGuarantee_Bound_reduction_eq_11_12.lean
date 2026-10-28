-- Prove2me | solution 1 for ProviderGuarantee.Bound.reduction_eq_11_12
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-26T06:52:30.059919+00:00
-- url     : https://prove2.me/submissions/908c1108-495e-469f-a479-110245caf98c

import Definitions.Def_ProviderGuarantee_Bound_Model
import Init
import Mathlib


section
namespace Queelius.ProviderGuarantee.Community.HartmannPsi
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

end Queelius.ProviderGuarantee.Community.HartmannPsi

end

section
noncomputable section
namespace Queelius.ProviderGuarantee
open ProviderGuarantee.Bound

theorem heterogeneity_range (a b : ℝ) (ha : 0  <  a) (hab : a ≤ b) :
    0 ≤ heterogeneity a b ∧ heterogeneity a b < 1 := by
  have hb : 0  <  b:=ha.trans_le hab
  unfold heterogeneity
  constructor
  · exact div_nonneg (sub_nonneg.mpr hab) hb.le
  · apply (div_lt_one hb).mpr
    linarith

theorem vertex_value_antitone (n m l : ℕ) (hm : 1 ≤ m) (hml : m ≤ l) (hln : l ≤ n)
    (δ : ℝ) (hd0 : 0 ≤ δ) (hd1 : δ < 1) : lemma2Value n l δ ≤ lemma2Value n m δ := by
  have hmn : m ≤ n:=hml.trans hln
  have hn : 1 ≤ n:=hm.trans hmn
  have hmR : (1:ℝ) ≤ m:=by exact_mod_cast hm
  have hnR : (1:ℝ) ≤ n:=by exact_mod_cast hn
  have hmlR : (m:ℝ) ≤ l:=by exact_mod_cast hml
  have hlnR : (l:ℝ) ≤ n:=by exact_mod_cast hln
  have hmnR : (m:ℝ) ≤ n:=hmlR.trans hlnR
  have hden : 0  <  (n:ℝ)+m+(1-δ)*((n:ℝ)-m)-1 := by
    have hp:=mul_nonneg (show 0 ≤ 1-δ by linarith) (sub_nonneg.mpr hmnR)
    linarith
  have horder : (n:ℝ)+m+(1-δ)*((n:ℝ)-m)-1 ≤ (n:ℝ)+l+(1-δ)*((n:ℝ)-l)-1 := by
    nlinarith [mul_nonneg hd0 (sub_nonneg.mpr hmlR)]
  unfold lemma2Value
  apply max_le_max_left
  exact div_le_div_of_nonneg_left (by linarith) hden horder

theorem first_vertex_bound (n : ℕ) (δ : ℝ) : lemma2Value n 1 δ=lossBound n δ := by
  unfold lemma2Value lossBound
  norm_num only [Nat.cast_one]
  congr 2
  ring

theorem vertex_order_all (n : ℕ) (a b : ℝ) (ha : 0  <  a) (hab : a ≤ b)
    (m l : ℕ) (hm : 1 ≤ m) (hml : m ≤ l) (hln : l ≤ n) :
    lemma2Value n l (heterogeneity a b) ≤ lemma2Value n m (heterogeneity a b) ∧
    lemma2Value n 1 (heterogeneity a b)=lossBound n (heterogeneity a b) := by
  have hd:=heterogeneity_range a b ha hab
  exact ⟨vertex_value_antitone n m l hm hml hln _ hd.1 hd.2,first_vertex_bound _ _⟩
end Queelius.ProviderGuarantee

end

section
noncomputable section
open Finset
namespace Queelius.ProviderGuarantee
variable {n : ℕ}

theorem coordinate_endpoint (a b x : Fin n → ℝ) (f : (Fin n → ℝ) → ℝ)
    (hf : QuasiconvexOn ℝ (Set.Icc a b) f) (hx : x∈Set.Icc a b) (i : Fin n) :
    ∃ y∈Set.Icc a b,(y i=a i ∨ y i=b i) ∧ (∀ j,j≠i→y j=x j) ∧ f x≤f y := by
  have hab : a i≤b i := (hx.1 i).trans (hx.2 i)
  by_cases he : a i=b i
  · exact ⟨x,hx,Or.inl (le_antisymm (by simpa [he] using hx.2 i) (hx.1 i)),
      fun _ _=>rfl,le_rfl⟩
  have hd : 0<b i-a i := sub_pos.mpr (lt_of_le_of_ne hab he)
  let l:=Function.update x i (a i)
  let r:=Function.update x i (b i)
  have hl : l∈Set.Icc a b := by
    constructor <;> intro j <;> by_cases h : j=i
    · subst j;simp [l]
    · simpa [l,h] using hx.1 j
    · subst j;simpa [l] using hab
    · simpa [l,h] using hx.2 j
  have hr : r∈Set.Icc a b := by
    constructor <;> intro j <;> by_cases h : j=i
    · subst j;simpa [r] using hab
    · simpa [r,h] using hx.1 j
    · subst j;simp [r]
    · simpa [r,h] using hx.2 j
  let t:ℝ:=(b i-x i)/(b i-a i)
  let u:ℝ:=(x i-a i)/(b i-a i)
  have ht : 0≤t := div_nonneg (sub_nonneg.mpr (hx.2 i)) hd.le
  have hu : 0≤u := div_nonneg (sub_nonneg.mpr (hx.1 i)) hd.le
  have hsum : t+u=1 := by dsimp [t,u];field_simp;ring
  have hmix : t • l+u • r=x := by
    funext j
    by_cases h : j=i
    · subst j
      simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,l,r,Function.update_self]
      dsimp [t,u]
      field_simp
      ring
    · simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,l,r,Function.update_of_ne h]
      rw [←add_mul,hsum,one_mul]
  have hbound := (quasiconvexOn_iff_le_max.mp hf).2 hl hr ht hu hsum
  rw [hmix] at hbound
  rcases le_max_iff.mp hbound with h|h
  · exact ⟨l,hl,Or.inl (by simp [l]),fun j hj=>by simp [l,hj],h⟩
  · exact ⟨r,hr,Or.inr (by simp [r]),fun j hj=>by simp [r,hj],h⟩

theorem box_vertex (a b : Fin n → ℝ) (f : (Fin n → ℝ) → ℝ)
    (hf : QuasiconvexOn ℝ (Set.Icc a b) f) :
    ∀ x∈Set.Icc a b,∃ y∈Set.Icc a b,(∀ i,y i=a i ∨ y i=b i) ∧ f x≤f y := by
  have finish (S : Finset (Fin n)) : ∀ x∈Set.Icc a b,
      (∀ i,i∉S→x i=a i ∨ x i=b i)→
      ∃ y∈Set.Icc a b,(∀ i,y i=a i ∨ y i=b i) ∧ f x≤f y := by
    induction S using Finset.induction_on with
    | empty =>
      intro x hx hout
      exact ⟨x,hx,fun i=>hout i (notMem_empty i),le_rfl⟩
    | @insert i S hi ih =>
      intro x hx hout
      obtain ⟨z,hz,he,hpres,hfx⟩:=coordinate_endpoint a b x f hf hx i
      have houtz : ∀ j,j∉S→z j=a j ∨ z j=b j := by
        intro j hj
        by_cases h : j=i
        · subst j;exact he
        · rw [hpres j h]
          exact hout j (by simp [h,hj])
      obtain ⟨y,hy,he,hfy⟩:=ih z hz houtz
      exact ⟨y,hy,he,hfx.trans hfy⟩
  intro x hx
  exact finish univ x hx (fun i hi=>False.elim (hi (mem_univ i)))
end Queelius.ProviderGuarantee

end

section
noncomputable section
open Finset
namespace Queelius.ProviderGuarantee
open ProviderGuarantee.Bound
variable {n : ℕ}

theorem weight_sum_pos (hn : 0 < n) (γ : Fin n → ℝ) (hγ : ∀ i, 0 < γ i) :
    0 < ∑ i, γ i := by
  exact sum_pos (fun i _ => hγ i) ⟨⟨0,hn⟩,mem_univ _⟩

theorem constant_primal (hn : 0 < n) (γ : Fin n → ℝ) (hγ : ∀ i, 0 < γ i) :
    PrimalFeasible γ (fun _=> (∑ i,γ i)⁻¹) (fun _=> (∑ i,γ i)⁻¹) (fun _ _=>0) := by
  have hp := weight_sum_pos hn γ hγ
  refine ⟨?_,?_,?_,?_,?_⟩
  · simp only [zero_mul,sum_const_zero,add_zero]
    rw [←sum_mul,mul_inv_cancel₀ hp.ne']
  · intro i j
    simp
  · intro i
    exact inv_nonneg.mpr hp.le
  · intro i
    exact inv_nonneg.mpr hp.le
  · intro i j
    rfl

theorem constant_primal_objective (γ : Fin n → ℝ) (a : ℝ) :
    primalObj γ (fun _=>a) (fun _=>a) (fun _ _=>0)=0 := by
  simp [primalObj]

theorem primal_objective_identity (γ x y : Fin n → ℝ) (w : Fin n → Fin n → ℝ)
    (hf : PrimalFeasible γ x y w) :
    primalObj γ x y w=1-(∑ i,γ i*y i)-(∑ i,∑ j,w i j*γ j) := by
  unfold primalObj
  simp_rw [mul_sub,sum_sub_distrib]
  linarith [hf.1]

theorem primal_objective_le_one (γ x y : Fin n → ℝ) (w : Fin n → Fin n → ℝ)
    (hγ : ∀ i,0≤γ i) (hf : PrimalFeasible γ x y w) : primalObj γ x y w≤1 := by
  rw [primal_objective_identity γ x y w hf]
  have hy : 0≤∑ i,γ i*y i := sum_nonneg (fun i _=>mul_nonneg (hγ i) (hf.2.2.2.1 i))
  have hw : 0≤∑ i,∑ j,w i j*γ j := sum_nonneg (fun i _=>sum_nonneg (fun j _=>mul_nonneg (hf.2.2.2.2 i j) (hγ j)))
  linarith

theorem well_posed (hn : 0 < n) (γ : Fin n → ℝ) (hγ : ∀ i,0 < γ i) :
    (∃ x y : Fin n → ℝ,∃ w : Fin n → Fin n → ℝ,PrimalFeasible γ x y w) ∧
    (∀ x y w,PrimalFeasible γ x y w→primalObj γ x y w≤1) ∧ 0≤lpValue γ ∧ lpValue γ≤1 := by
  have hf:=constant_primal hn γ hγ
  have hub := fun x y w h => primal_objective_le_one γ x y w (fun i=>(hγ i).le) h
  have hb : BddAbove {z | ∃ x y : Fin n → ℝ,∃ w : Fin n → Fin n → ℝ,
      PrimalFeasible γ x y w ∧ z=primalObj γ x y w} := by
    refine ⟨1,?_⟩
    rintro z ⟨x,y,w,h,rfl⟩
    exact hub x y w h
  have hz : (0:ℝ)∈{z | ∃ x y : Fin n → ℝ,∃ w : Fin n → Fin n → ℝ,
      PrimalFeasible γ x y w ∧ z=primalObj γ x y w} :=
    ⟨_,_,_,hf,(constant_primal_objective γ _).symm⟩
  refine ⟨⟨_,_,_,hf⟩,hub,le_csSup hb hz,csSup_le ⟨0,hz⟩ ?_⟩
  rintro z ⟨x,y,w,h,rfl⟩
  exact hub x y w h

theorem unit_dual (γ : Fin n → ℝ) (hγ : ∀ i,0≤γ i) : DualFeasible γ 1 (fun _ _=>0) := by
  refine ⟨?_,?_,?_,?_⟩
  · intro i
    simp
  · intro k j
    simpa using hγ j
  · intro j
    simpa using hγ j
  · intro i j
    rfl
end Queelius.ProviderGuarantee

end

section
noncomputable section
open Finset Classical
namespace Queelius.ProviderGuarantee
open ProviderGuarantee.Bound
variable {D : Type*} [Fintype D] [DecidableEq D] {n : ℕ}

theorem update_strict_improvement (γ : Fin n → ℝ) (v : D → ℝ)
    (B : Fin n → Finset D) (j : Fin n) (T : Finset D)
    (hγ : 0 < γ j) (hv : val v (B j) < val v T) :
    totalValue γ v B < totalValue γ v (Function.update B j T) := by
  unfold totalValue
  apply sum_lt_sum
  · intro i _
    by_cases hi : i=j
    · subst i
      simp only [Function.update_self]
      exact (mul_lt_mul_of_pos_left hv hγ).le
    · simp only [Function.update_of_ne hi]
      exact le_rfl
  · exact ⟨j,mem_univ _,by simpa only [Function.update_self] using mul_lt_mul_of_pos_left hv hγ⟩

theorem exchange_from_feasible (v : D → ℝ) (γ : Fin n → ℝ) (hγ : ∀ j,0 < γ j)
    (F FG : Set (Fin n → Finset D)) (h1 : Assumption1 F) (h2 : Assumption2 v F FG)
    (A B : Fin n → Finset D) (hA : A ∈ F) (hB : IsOptimal γ v FG B) (i j : Fin n) :
    val v (A i \ univ.biUnion B) ≤ val v (B j \ A i) := by
  by_contra hn
  have hlt : val v (B j \ A i) < val v (A i \ univ.biUnion B) := lt_of_not_ge hn
  let T : Finset D := (B j ∩ A i) ∪ (A i \ univ.biUnion B)
  have hBF : B ∈ F:=h2.1 hB.1
  have hdis : Disjoint (B j ∩ A i) (A i \ univ.biUnion B) := by
    apply disjoint_left.mpr
    intro d hd ht
    exact (mem_sdiff.mp ht).2 (mem_biUnion.mpr ⟨j,mem_univ _,(mem_inter.mp hd).1⟩)
  have hval : val v (B j) < val v T := by
    have hp:=sum_inter_add_sum_sdiff (B j) (A i) v
    dsimp [T,ProviderGuarantee.Bound.val]
    rw [sum_union hdis]
    unfold ProviderGuarantee.Bound.val at hlt
    linarith
  have hsub : T ⊆ A i := union_subset inter_subset_right sdiff_subset
  let A' : Fin n → Finset D := fun k=>A (Equiv.swap i j k)
  have hAF : A' ∈ F:=h1.2.1 A hA (Equiv.swap i j)
  have haj : A' j=A i := by simp [A']
  have hTsub : T ⊆ A' j := by rwa [haj]
  have hTF : Function.update A' j T ∈ F:=h1.2.2.1 A' hAF j T hTsub
  have hTB : Function.update B j T ∈ F := by
    have hh:=h1.2.2.2 (Function.update A' j T) hTF B hBF j
    simp only [Function.update_self] at hh
    apply hh
    intro k hk
    apply disjoint_left.mpr
    intro d hd hdk
    rcases mem_union.mp hd with hd | hd
    · exact disjoint_left.mp (h1.1 B hBF j k (Ne.symm hk)) (mem_inter.mp hd).1 hdk
    · exact (mem_sdiff.mp hd).2 (mem_biUnion.mpr ⟨k,mem_univ _,hdk⟩)
  have hTG : Function.update B j T ∈ FG := by
    apply h2.2 B hB.1 (Function.update B j T) hTB
    intro k
    by_cases hk : k=j
    · subst k
      simpa only [Function.update_self] using hval.le
    · simp only [Function.update_of_ne hk]
      exact le_rfl
  exact (not_lt_of_ge (hB.2 _ hTG)) (update_strict_improvement γ v B j T (hγ j) hval)

theorem guaranteed_job_nonneg (v : D → ℝ) (γ : Fin n → ℝ) (hγ : ∀ j,0 < γ j)
    (F FG : Set (Fin n → Finset D)) (h1 : Assumption1 F) (h2 : Assumption2 v F FG)
    (B : Fin n → Finset D) (hB : IsOptimal γ v FG B) (i : Fin n) (d : D) (hd : d ∈ B i) :
    0 ≤ v d := by
  by_contra hn
  have hv : v d < 0 := lt_of_not_ge hn
  have he : val v ((B i).erase d)+v d=val v (B i) := by
    exact sum_erase_add _ _ hd
  have hval : val v (B i) < val v ((B i).erase d) := by linarith
  have hF : Function.update B i ((B i).erase d) ∈ F :=
    h1.2.2.1 B (h2.1 hB.1) i _ (erase_subset _ _)
  have hG : Function.update B i ((B i).erase d) ∈ FG := by
    apply h2.2 B hB.1 _ hF
    intro j
    by_cases hj : j=i
    · subst j
      simpa only [Function.update_self] using hval.le
    · simp only [Function.update_of_ne hj]
      exact le_rfl
  exact (not_lt_of_ge (hB.2 _ hG)) (update_strict_improvement γ v B i _ (hγ i) hval)

theorem unrestricted_job_nonneg (v : D → ℝ) (γ : Fin n → ℝ) (hγ : ∀ j,0 < γ j)
    (F : Set (Fin n → Finset D)) (h1 : Assumption1 F)
    (A : Fin n → Finset D) (hA : IsOptimal γ v F A) (i : Fin n) (d : D) (hd : d ∈ A i) :
    0 ≤ v d :=
  guaranteed_job_nonneg v γ hγ F F h1 ⟨Set.Subset.rfl,fun _ _ _ h _=>h⟩ A hA i d hd
end Queelius.ProviderGuarantee

end

section
noncomputable section
open scoped BigOperators
open Matrix
namespace Queelius.ProviderGuarantee

/-- Reindex the credited standard-form LP theorem along arbitrary finite row/column types. -/
theorem finite_lp_duality {R C : Type*} [Fintype R] [Fintype C]
    (A : Matrix R C ℝ) (d : C → ℝ) (g : R → ℝ) (x : C → ℝ)
    (hx : ∀ c, 0 ≤ x c) (hAx : ∀ r, ∑ c, A r c * x c = g r)
    (hopt : ∀ y : C → ℝ, (∀ c, 0 ≤ y c) → (∀ r, ∑ c, A r c * y c = g r) →
      (∑ c, d c * x c) ≤ ∑ c, d c * y c) :
    ∃ p : R → ℝ, (∀ c, ∑ r, A r c * p r ≤ d c) ∧
      (∑ r, g r * p r) = ∑ c, d c * x c := by
  classical
  let er := (Fintype.equivFin R).symm
  let ec := (Fintype.equivFin C).symm
  let A' : Matrix (Fin (Fintype.card R)) (Fin (Fintype.card C)) ℝ :=
    fun i j => A (er i) (ec j)
  have hA' : A'.mulVec (fun j => x (ec j)) = fun i => g (er i) := by
    funext i
    exact (ec.sum_comp (fun c => A (er i) c * x c)).trans (hAx (er i))
  have hopt' (y : Fin (Fintype.card C) → ℝ) (hy : ∀ j, 0 ≤ y j)
      (hAy : A'.mulVec y = fun i => g (er i)) :
      dotProduct (fun j => d (ec j)) (fun j => x (ec j)) ≤ dotProduct (fun j => d (ec j)) y := by
    have hrow (r : R) : ∑ c, A r c * y (ec.symm c) = g r := by
      have h := congrFun hAy (er.symm r)
      have hre := ec.symm.sum_comp (fun j => A r (ec j) * y j)
      simp only [Equiv.apply_symm_apply] at hre
      simpa only [Matrix.mulVec, dotProduct, A', Equiv.apply_symm_apply, ← hre] using h
    have h := hopt (fun c => y (ec.symm c)) (fun c => hy _) hrow
    have h1 := ec.sum_comp (fun c => d c * x c)
    have h2 := ec.symm.sum_comp (fun j => d (ec j) * y j)
    simp only [Equiv.apply_symm_apply] at h2
    exact h1.trans_le (h.trans_eq h2)
  obtain ⟨p,hp,heq,_⟩ := Community.HartmannPsi.LPBasic.lp_strong_duality A'
    (fun j => d (ec j)) (fun i => g (er i)) (fun j => x (ec j))
    (fun j => hx _) hA' hopt'
  refine ⟨fun r => p (er.symm r), ?_, ?_⟩
  · intro c
    have h := hp (ec.symm c)
    have hr := er.symm.sum_comp (fun i => A (er i) c * p i)
    simp only [Equiv.apply_symm_apply] at hr
    change (∑ i, A (er i) (ec (ec.symm c)) * p i) ≤ d (ec (ec.symm c)) at h
    simpa only [Equiv.apply_symm_apply, ← hr] using h
  · have hr := er.symm.sum_comp (fun i => g (er i) * p i)
    simp only [Equiv.apply_symm_apply] at hr
    exact hr.trans (heq.trans (ec.sum_comp (fun c => d c * x c)))

end Queelius.ProviderGuarantee

end

section
noncomputable section
open Finset
namespace Queelius.ProviderGuarantee
open ProviderGuarantee.Bound
variable {n : ℕ}

theorem weighted_slack_identity (x y : Fin n → ℝ) (w lam : Fin n → Fin n → ℝ) :
    (∑ i,∑ j,lam i j*(y j+(∑ k,w k j)-x i-w i j)) =
    (∑ j,y j*(∑ i,lam i j))+
    (∑ k,∑ j,w k j*((∑ i,lam i j)-lam k j))-
    (∑ i,x i*(∑ j,lam i j)) := by
  have hy : (∑ i,∑ j,lam i j*y j)=∑ j,y j*(∑ i,lam i j) := by
    rw [sum_comm]
    simp only [mul_sum,mul_comm]
  have hx : (∑ i,∑ j,lam i j*x i)=∑ i,x i*(∑ j,lam i j) := by
    simp only [mul_sum,mul_comm]
  have hw : (∑ i,∑ j,lam i j*(∑ k,w k j))=∑ k,∑ j,w k j*(∑ i,lam i j) := by
    simp only [mul_sum]
    conv_lhs =>
      rw [sum_comm]
      arg 2
      ext j
      rw [sum_comm]
    rw [sum_comm]
    simp only [mul_comm]
  simp only [mul_sub,mul_add,sum_sub_distrib,sum_add_distrib]
  rw [hy,hx,hw]
  simp only [mul_comm]
  ring

theorem weighted_primal_slack (γ x y : Fin n → ℝ) (w lam : Fin n → Fin n → ℝ)
    (hp : PrimalFeasible γ x y w) (hlam : ∀ i j,0≤lam i j) :
    (∑ i,x i*(∑ j,lam i j))≤(∑ j,y j*(∑ i,lam i j))+
      (∑ k,∑ j,w k j*((∑ i,lam i j)-lam k j)) := by
  have h : 0≤∑ i,∑ j,lam i j*(y j+(∑ k,w k j)-x i-w i j) := by
    apply sum_nonneg
    intro i _
    apply sum_nonneg
    intro j _
    apply mul_nonneg (hlam i j)
    linarith [hp.2.1 i j]
  rw [weighted_slack_identity] at h
  linarith

theorem weak_duality (γ x y : Fin n → ℝ) (w : Fin n → Fin n → ℝ)
    (s : ℝ) (lam : Fin n → Fin n → ℝ)
    (hp : PrimalFeasible γ x y w) (hd : DualFeasible γ s lam) : primalObj γ x y w ≤ s := by
  have hx : (∑ i,γ i*x i) ≤ s*(∑ i,γ i*x i)+(∑ i,x i*(∑ j,lam i j)) := by
    have h:=sum_le_sum (fun i (_ : i∈(univ : Finset (Fin n)))=>
      mul_le_mul_of_nonneg_right (hd.1 i) (hp.2.2.1 i))
    simpa only [add_mul,mul_add,sum_add_distrib,mul_assoc,mul_sum,mul_comm,mul_left_comm] using h
  have hy : (∑ j,y j*(∑ i,lam i j))≤∑ j,γ j*y j := by
    apply sum_le_sum
    intro j _
    simpa only [mul_comm] using mul_le_mul_of_nonneg_right (hd.2.2.1 j) (hp.2.2.2.1 j)
  have hw : (∑ k,∑ j,w k j*γ k)-(∑ k,∑ j,w k j*γ j) ≤
      s*(∑ k,∑ j,w k j*γ k)-(∑ k,∑ j,w k j*((∑ i,lam i j)-lam k j)) := by
    have h : (∑ k,∑ j,w k j*(γ k-γ j))≤
        ∑ k,∑ j,w k j*(s*γ k-((∑ i,lam i j)-lam k j)) := by
      apply sum_le_sum
      intro k _
      apply sum_le_sum
      intro j _
      apply mul_le_mul_of_nonneg_left _ (hp.2.2.2.2 k j)
      have he:=sum_erase_add univ (fun i=>lam i j) (mem_univ k)
      linarith [hd.2.1 k j]
    simpa only [mul_sub,sum_sub_distrib,mul_sum,mul_assoc,mul_comm,mul_left_comm] using h
  have hs:=weighted_primal_slack γ x y w lam hp hd.2.2.2
  have hn : s*(∑ i,γ i*x i)+s*(∑ i,∑ j,w i j*γ i)=s := by
    rw [←mul_add,hp.1,mul_one]
  unfold primalObj
  simp_rw [mul_sub,sum_sub_distrib]
  linarith

theorem dual_objective_nonneg (hn : 0<n) (γ : Fin n → ℝ) (hγ : ∀ i,0<γ i)
    (s : ℝ) (lam : Fin n → Fin n → ℝ) (hd : DualFeasible γ s lam) : 0 ≤ s := by
  have h:=weak_duality γ _ _ _ s lam (constant_primal hn γ hγ) hd
  simpa only [constant_primal_objective] using h

theorem lp_le_dual_certificate (hn : 0<n) (γ : Fin n → ℝ) (hγ : ∀ i,0<γ i)
    (s : ℝ) (lam : Fin n → Fin n → ℝ) (hd : DualFeasible γ s lam) : lpValue γ ≤ s := by
  apply csSup_le
  · exact ⟨0,_,_,_,constant_primal hn γ hγ,(constant_primal_objective γ _).symm⟩
  · rintro z ⟨x,y,w,hp,rfl⟩
    exact weak_duality γ x y w s lam hp hd

theorem dual_value_bounds (hn : 0<n) (γ : Fin n → ℝ) (hγ : ∀ i,0<γ i) :
    0≤dualValue γ ∧ dualValue γ≤1 ∧ lpValue γ≤dualValue γ := by
  have he : (1:ℝ)∈{s | ∃ lam : Fin n → Fin n → ℝ,DualFeasible γ s lam}:=
    ⟨_,unit_dual γ (fun i=>(hγ i).le)⟩
  have hb : BddBelow {s | ∃ lam : Fin n → Fin n → ℝ,DualFeasible γ s lam} := by
    refine ⟨0,?_⟩
    rintro s ⟨lam,hd⟩
    exact dual_objective_nonneg hn γ hγ s lam hd
  refine ⟨le_csInf ⟨1,he⟩ ?_,csInf_le hb he,le_csInf ⟨1,he⟩ ?_⟩
  · rintro s ⟨lam,hd⟩
    exact dual_objective_nonneg hn γ hγ s lam hd
  · rintro s ⟨lam,hd⟩
    exact lp_le_dual_certificate hn γ hγ s lam hd
end Queelius.ProviderGuarantee
namespace Queelius.ProviderGuarantee
open ProviderGuarantee.Bound Finset

theorem dual_value_le_certificate {n : ℕ} (hn : 0<n) (γ : Fin n → ℝ) (hγ : ∀ i,0<γ i)
    (s : ℝ) (lam : Fin n → Fin n → ℝ) (hd : DualFeasible γ s lam) : dualValue γ ≤ s := by
  apply csInf_le
  · refine ⟨0,?_⟩
    rintro t ⟨mu,ht⟩
    exact dual_objective_nonneg hn γ hγ t mu ht
  · exact ⟨lam,hd⟩
end Queelius.ProviderGuarantee

end

section
noncomputable section
open Finset Set
namespace Queelius.ProviderGuarantee
open ProviderGuarantee.Bound
variable {n : ℕ}

abbrev PrimalPoint (n:ℕ) := (Fin n→ℝ)×(Fin n→ℝ)×(Fin n→Fin n→ℝ)

def primalSet (γ:Fin n→ℝ) : Set (PrimalPoint n) := {p|PrimalFeasible γ p.1 p.2.1 p.2.2}
def primalBox (B:ℝ) : Set (PrimalPoint n) := Icc (0,0,0) (fun _=>B,fun _=>B,fun _ _=>B)

theorem primal_set_closed (γ:Fin n→ℝ) : IsClosed (primalSet γ) := by
  have h1 : IsClosed {p:PrimalPoint n | (∑i,γ i*p.1 i)+(∑i,∑j,p.2.2 i j*γ i)=1}:=
    isClosed_eq (by fun_prop) continuous_const
  have h2 : IsClosed {p:PrimalPoint n | ∀i j,p.1 i+p.2.2 i j-(∑k,p.2.2 k j)-p.2.1 j≤0} := by
    simp only [ofPred_forall]
    exact isClosed_iInter (fun i=>isClosed_iInter (fun j=>isClosed_le (by fun_prop) continuous_const))
  have h3 : IsClosed {p:PrimalPoint n | ∀i,0≤p.1 i} := by
    simp only [ofPred_forall]
    exact isClosed_iInter (fun i=>isClosed_le continuous_const (by fun_prop))
  have h4 : IsClosed {p:PrimalPoint n | ∀i,0≤p.2.1 i} := by
    simp only [ofPred_forall]
    exact isClosed_iInter (fun i=>isClosed_le continuous_const (by fun_prop))
  have h5 : IsClosed {p:PrimalPoint n | ∀i j,0≤p.2.2 i j} := by
    simp only [ofPred_forall]
    exact isClosed_iInter (fun i=>isClosed_iInter (fun j=>isClosed_le continuous_const (by fun_prop)))
  exact h1.inter (h2.inter (h3.inter (h4.inter h5)))

theorem primal_objective_continuous (γ:Fin n→ℝ) :
    Continuous (fun p:PrimalPoint n=>primalObj γ p.1 p.2.1 p.2.2) := by
  unfold primalObj
  fun_prop

theorem primal_coordinate_bounds (γ x y:Fin n→ℝ) (w:Fin n→Fin n→ℝ)
    (hγ:∀i,0<γ i) (hp:PrimalFeasible γ x y w) :
    (∀i,x i≤(γ i)⁻¹) ∧ (∀i j,w i j≤(γ i)⁻¹) := by
  have hx0 : 0≤∑i,γ i*x i:=sum_nonneg (fun i _=>mul_nonneg (hγ i).le (hp.2.2.1 i))
  have hw0 : 0≤∑i,∑j,w i j*γ i:=sum_nonneg (fun i _=>sum_nonneg (fun j _=>mul_nonneg (hp.2.2.2.2 i j) (hγ i).le))
  constructor
  · intro i
    have hi:=single_le_sum (fun k (_:k∈(univ:Finset (Fin n)))=>mul_nonneg (hγ k).le (hp.2.2.1 k)) (mem_univ i)
    rw [inv_eq_one_div]
    apply (le_div_iff₀ (hγ i)).mpr
    nlinarith [hp.1]
  · intro i j
    have hi:=single_le_sum (fun k (_:k∈(univ:Finset (Fin n)))=>sum_nonneg (fun l (_:l∈(univ:Finset (Fin n)))=>mul_nonneg (hp.2.2.2.2 k l) (hγ k).le)) (mem_univ i)
    have hj:=single_le_sum (fun l (_:l∈(univ:Finset (Fin n)))=>mul_nonneg (hp.2.2.2.2 i l) (hγ i).le) (mem_univ j)
    rw [inv_eq_one_div]
    apply (le_div_iff₀ (hγ i)).mpr
    nlinarith [hp.1]

theorem clamp_primal (γ x y:Fin n→ℝ) (w:Fin n→Fin n→ℝ) (B:ℝ)
    (hγ:∀i,0≤γ i) (hB:0≤B) (hx:∀i,x i≤B) (hp:PrimalFeasible γ x y w) :
    PrimalFeasible γ x (fun j=>min (y j) B) w ∧
      primalObj γ x y w≤primalObj γ x (fun j=>min (y j) B) w := by
  constructor
  · refine ⟨hp.1,?_,hp.2.2.1,fun j=>le_min (hp.2.2.2.1 j) hB,hp.2.2.2.2⟩
    intro i j
    have hw : w i j≤∑k,w k j:=single_le_sum (fun k (_:k∈(univ:Finset (Fin n)))=>hp.2.2.2.2 k j) (mem_univ i)
    have hle : x i+w i j-(∑k,w k j)≤ min (y j) B := le_min (by linarith [hp.2.1 i j]) (by linarith [hx i])
    linarith
  · have hsum:=sum_le_sum (fun j (_:j∈(univ:Finset (Fin n)))=>mul_le_mul_of_nonneg_left (min_le_left (y j) B) (hγ j))
    unfold primalObj
    linarith

theorem primal_attained (hn:0<n) (γ:Fin n→ℝ) (hγ:∀i,0<γ i) :
    ∃x y:Fin n→ℝ,∃w:Fin n→Fin n→ℝ,PrimalFeasible γ x y w ∧ primalObj γ x y w=lpValue γ := by
  let B:=∑i,(γ i)⁻¹
  have hB : 0≤B:=sum_nonneg (fun i _=>(inv_pos.mpr (hγ i)).le)
  have hiB (i:Fin n) : (γ i)⁻¹≤B:=single_le_sum (fun j (_:j∈(univ:Finset (Fin n)))=>(inv_pos.mpr (hγ j)).le) (mem_univ i)
  have project (x y:Fin n→ℝ) (w:Fin n→Fin n→ℝ) (hp:PrimalFeasible γ x y w) :
      ∃p∈primalSet γ∩primalBox B,primalObj γ x y w≤primalObj γ p.1 p.2.1 p.2.2 := by
    have hb:=primal_coordinate_bounds γ x y w hγ hp
    have hc:=clamp_primal γ x y w B (fun i=>(hγ i).le) hB (fun i=>(hb.1 i).trans (hiB i)) hp
    refine ⟨(x,(fun j=>min (y j) B),w),⟨hc.1,?_⟩,hc.2⟩
    exact ⟨⟨hp.2.2.1,fun j=>le_min (hp.2.2.2.1 j) hB,hp.2.2.2.2⟩,
      ⟨fun i=>(hb.1 i).trans (hiB i),fun j=>min_le_right (y j) B,fun i j=>(hb.2 i j).trans (hiB i)⟩⟩
  have hc : IsCompact (primalSet γ∩primalBox B):=isCompact_Icc.inter_left (primal_set_closed γ)
  obtain ⟨p,hp,_⟩:=project _ _ _ (constant_primal hn γ hγ)
  obtain ⟨q,hq,hmax⟩:=hc.exists_isMaxOn ⟨p,hp⟩ (primal_objective_continuous γ).continuousOn
  have hqf : PrimalFeasible γ q.1 q.2.1 q.2.2:=hq.1
  refine ⟨q.1,q.2.1,q.2.2,hqf,le_antisymm ?_ ?_⟩
  · change primalObj γ q.1 q.2.1 q.2.2 ≤ sSup {z | ∃x y:Fin n→ℝ,∃w:Fin n→Fin n→ℝ,PrimalFeasible γ x y w ∧ z=primalObj γ x y w}
    apply le_csSup
    · refine ⟨1,?_⟩
      rintro z ⟨x,y,w,h,rfl⟩
      exact primal_objective_le_one γ x y w (fun i=>(hγ i).le) h
    · exact ⟨q.1,q.2.1,q.2.2,hqf,rfl⟩
  · change sSup {z | ∃x y:Fin n→ℝ,∃w:Fin n→Fin n→ℝ,PrimalFeasible γ x y w ∧ z=primalObj γ x y w} ≤ primalObj γ q.1 q.2.1 q.2.2
    apply csSup_le
    · exact ⟨_,q.1,q.2.1,q.2.2,hqf,rfl⟩
    rintro z ⟨x,y,w,h,rfl⟩
    obtain ⟨p,hp,hle⟩:=project x y w h
    exact hle.trans (hmax hp)
end Queelius.ProviderGuarantee

end

section
namespace ProviderGuarantee.Bound

theorem lp_well_posed {n : ℕ} (hn : 0 < n) (γ : Fin n → ℝ) (hγ : ∀ i, 0 < γ i) :
    (∃ x y : Fin n → ℝ, ∃ w : Fin n → Fin n → ℝ, PrimalFeasible γ x y w) ∧
    (∀ (x y : Fin n → ℝ) (w : Fin n → Fin n → ℝ), PrimalFeasible γ x y w →
      primalObj γ x y w ≤ 1) ∧
    0 ≤ lpValue γ ∧ lpValue γ ≤ 1 := by
  exact Queelius.ProviderGuarantee.well_posed hn γ hγ

end ProviderGuarantee.Bound

namespace ProviderGuarantee.Bound

theorem quasiconvexOn_box_vertex {n : ℕ} (a b : Fin n → ℝ) (f : (Fin n → ℝ) → ℝ)
    (hf : QuasiconvexOn ℝ (Set.Icc a b) f) :
    ∀ x ∈ Set.Icc a b, ∃ y ∈ Set.Icc a b, (∀ i, y i = a i ∨ y i = b i) ∧ f x ≤ f y := by
  exact Queelius.ProviderGuarantee.box_vertex a b f hf

end ProviderGuarantee.Bound

end

section
noncomputable section
open Finset
namespace Queelius.ProviderGuarantee
open ProviderGuarantee.Bound

theorem vertex_sum (n m : ℕ) (hm : m≤n) (a b : ℝ) :
    (∑ i : Fin n,if (i:ℕ) < m then b else a)=(m:ℝ)*b+((n:ℝ)-m)*a := by
  classical
  have hcard : (univ.filter (fun i : Fin n=>(i:ℕ) < m)).card=m := by
    rcases eq_or_lt_of_le hm with h|h
    · subst m
      simp only [Fin.is_lt,filter_true,card_univ,Fintype.card_fin]
    · have heq : univ.filter (fun i : Fin n=>(i:ℕ) < m)=Iio (⟨m,h⟩:Fin n) := by
        ext i
        simp [Fin.lt_def]
      rw [heq,Fin.card_Iio]
  have hcards:=card_filter_add_card_filter_not (s:=univ) (fun i : Fin n=>(i:ℕ) < m)
  rw [hcard,card_univ,Fintype.card_fin] at hcards
  have hlow : ((univ.filter (fun i : Fin n=>¬(i:ℕ) < m)).card:ℝ)=(n:ℝ)-m := by
    have hh : (m:ℝ)+(univ.filter (fun i : Fin n=>¬(i:ℕ) < m)).card=n := by exact_mod_cast hcards
    linarith
  rw [sum_ite]
  simp only [sum_const,nsmul_eq_mul,hcard,hlow]

theorem vertex_weight_bounds (n m : ℕ) (a b : ℝ) (hab : a≤b) (i : Fin n) :
    a≤vertexProfile n m a b i ∧ vertexProfile n m a b i≤b := by
  by_cases h:(i:ℕ) < m <;> simp [vertexProfile,h,hab]
end Queelius.ProviderGuarantee

end

section
noncomputable section
open Finset Classical
namespace Queelius.ProviderGuarantee
open ProviderGuarantee.Bound
variable {D : Type*} [Fintype D] [DecidableEq D] {n : ℕ}

theorem val_partition (v : D → ℝ) (T : Finset D) (B : Fin n → Finset D)
    (hB : ∀ i j,i ≠ j → Disjoint (B i) (B j)) :
    val v T=val v (T \ univ.biUnion B)+∑ j,val v (T ∩ B j) := by
  have he : T ∩ univ.biUnion B=univ.biUnion (fun j=>T ∩ B j) := by
    ext d
    simp only [mem_inter,mem_biUnion,mem_univ,true_and]
    aesop
  have hd : (↑(univ : Finset (Fin n)) : Set (Fin n)).PairwiseDisjoint (fun j=>T ∩ B j) := by
    intro i _ j _ hij
    exact (hB i j hij).mono inter_subset_right inter_subset_right
  have hsum : val v (T ∩ univ.biUnion B)=∑ j,val v (T ∩ B j) := by
    unfold ProviderGuarantee.Bound.val
    rw [he,sum_biUnion hd]
  have hpart:=sum_inter_add_sum_sdiff T (univ.biUnion B) v
  change val v (T ∩ univ.biUnion B)+val v (T \ univ.biUnion B)=val v T at hpart
  linarith

theorem max_value_of_optimal (γ : Fin n → ℝ) (v : D → ℝ)
    (F : Set (Fin n → Finset D)) (A : Fin n → Finset D) (hA : IsOptimal γ v F A) :
    maxValue γ v F=totalValue γ v A := by
  unfold maxValue
  have hm : totalValue γ v A ∈ totalValue γ v '' F := ⟨A,hA.1,rfl⟩
  apply le_antisymm
  · apply csSup_le ⟨_,hm⟩
    rintro z ⟨B,hB,rfl⟩
    exact hA.2 B hB
  · exact le_csSup (Set.toFinite _).bddAbove hm

theorem allocation_scalar_reduction (v : D → ℝ) (γ : Fin n → ℝ) (hγ : ∀ i,0 < γ i)
    (F FG : Set (Fin n → Finset D)) (h1 : Assumption1 F) (h2 : Assumption2 v F FG)
    (A B : Fin n → Finset D) (hA : IsOptimal γ v F A) (hB : IsOptimal γ v FG B) :
    let x : Fin n → ℝ:=fun i=>val v (A i \ univ.biUnion B)
    let y : Fin n → ℝ:=fun i=>val v (B i \ univ.biUnion A)
    let w : Fin n → Fin n → ℝ:=fun i j=>val v (A i ∩ B j)
    (∀ i j,x i≤∑ k,w k j-w i j+y j) ∧
    (∀ i,val v (A i)=x i+∑ j,w i j) ∧
    (∀ j,val v (B j)=y j+∑ i,w i j) ∧
    (∀ i,0≤x i) ∧ (∀ i,0≤y i) ∧ (∀ i j,0≤w i j) ∧
    valueLoss γ v F FG=
      (∑ i,γ i*x i-∑ i,γ i*y i+∑ i,∑ j,w i j*(γ i-γ j))/
      (∑ i,γ i*x i+∑ i,∑ j,w i j*γ i) := by
  dsimp only
  have hpairA:=h1.1 A hA.1
  have hpairB:=h1.1 B (h2.1 hB.1)
  have hdecompA (i : Fin n):=val_partition v (A i) B hpairB
  have hdecompB (j : Fin n) : val v (B j)=val v (B j \ univ.biUnion A)+∑ i,val v (A i ∩ B j) := by
    simpa only [inter_comm] using val_partition v (B j) A hpairA
  refine ⟨?_,hdecompA,hdecompB,?_,?_,?_,?_⟩
  · intro i j
    have hex:=exchange_from_feasible v γ hγ F FG h1 h2 A B hA.1 hB i j
    have hp:=sum_inter_add_sum_sdiff (B j) (A i) v
    change val v (B j ∩ A i)+val v (B j \ A i)=val v (B j) at hp
    rw [inter_comm] at hp
    have hdec:=hdecompB j
    linarith
  · intro i
    apply sum_nonneg
    intro d hd
    exact unrestricted_job_nonneg v γ hγ F h1 A hA i d (mem_sdiff.mp hd).1
  · intro i
    apply sum_nonneg
    intro d hd
    exact guaranteed_job_nonneg v γ hγ F FG h1 h2 B hB i d (mem_sdiff.mp hd).1
  · intro i j
    apply sum_nonneg
    intro d hd
    exact unrestricted_job_nonneg v γ hγ F h1 A hA i d (mem_inter.mp hd).1
  · unfold ProviderGuarantee.Bound.valueLoss
    rw [max_value_of_optimal γ v F A hA,max_value_of_optimal γ v FG B hB]
    have ha : totalValue γ v A=(∑ i,γ i*val v (A i \ univ.biUnion B))+
        ∑ i,∑ j,val v (A i ∩ B j)*γ i := by
      unfold totalValue
      simp_rw [hdecompA,mul_add,mul_sum,sum_add_distrib]
      congr 1
      apply sum_congr rfl
      intro i _
      apply sum_congr rfl
      intro j _
      ring
    have hb : totalValue γ v B=(∑ j,γ j*val v (B j \ univ.biUnion A))+
        ∑ i,∑ j,val v (A i ∩ B j)*γ j := by
      unfold totalValue
      simp_rw [hdecompB,mul_add,mul_sum,sum_add_distrib]
      congr 1
      rw [sum_comm]
      apply sum_congr rfl
      intro i _
      apply sum_congr rfl
      intro j _
      ring
    rw [ha,hb]
    congr 1
    simp_rw [mul_sub,sum_sub_distrib]
    ring
end Queelius.ProviderGuarantee

end

section
noncomputable section
open Finset Classical
namespace Queelius.ProviderGuarantee
open ProviderGuarantee.Bound
variable {n : ℕ}

theorem dual_certificate_raise (γ : Fin n → ℝ) (hγ : ∀ i,0≤γ i) (s t : ℝ)
    (hst : s≤t) (lam : Fin n → Fin n → ℝ) (h : DualFeasible γ s lam) :
    DualFeasible γ t lam := by
  refine ⟨?_,?_,h.2.2.1,h.2.2.2⟩
  · intro i
    have hh:=h.1 i
    have hm:=mul_le_mul_of_nonneg_right hst (hγ i)
    linarith
  · intro k j
    have hh:=h.2.1 k j
    have hm:=mul_le_mul_of_nonneg_right hst (hγ k)
    linarith

theorem fixed_value_dual_mix (γ η : Fin n → ℝ) (s a b : ℝ)
    (ha : 0≤a) (hb : 0≤b) (lam mu : Fin n → Fin n → ℝ)
    (hγ : DualFeasible γ s lam) (hη : DualFeasible η s mu) :
    DualFeasible (a • γ+b • η) s (fun i j=>a*lam i j+b*mu i j) := by
  have hs (i : Fin n) : (∑ j,(a*lam i j+b*mu i j))=a*(∑ j,lam i j)+b*(∑ j,mu i j) := by
    simp only [sum_add_distrib,mul_sum]
  have ht (j : Fin n) (T : Finset (Fin n)) :
      (∑ i∈T,(a*lam i j+b*mu i j))=a*(∑ i∈T,lam i j)+b*(∑ i∈T,mu i j) := by
    simp only [sum_add_distrib,mul_sum]
  refine ⟨?_,?_,?_ ,?_⟩
  · intro i
    simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,hs]
    have h1:=mul_le_mul_of_nonneg_left (hγ.1 i) ha
    have h2:=mul_le_mul_of_nonneg_left (hη.1 i) hb
    nlinarith
  · intro k j
    simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,ht]
    have h1:=mul_nonneg ha (hγ.2.1 k j)
    have h2:=mul_nonneg hb (hη.2.1 k j)
    nlinarith
  · intro j
    simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,ht]
    exact add_le_add (mul_le_mul_of_nonneg_left (hγ.2.2.1 j) ha)
      (mul_le_mul_of_nonneg_left (hη.2.2.1 j) hb)
  · intro i j
    exact add_nonneg (mul_nonneg ha (hγ.2.2.2 i j)) (mul_nonneg hb (hη.2.2.2 i j))
end Queelius.ProviderGuarantee

end

section
noncomputable section
open Finset Set
namespace Queelius.ProviderGuarantee
open ProviderGuarantee.Bound
variable {n:ℕ}

abbrev DualPoint (n:ℕ) := ℝ×(Fin n→Fin n→ℝ)
def dualSet (γ:Fin n→ℝ) : Set (DualPoint n) := {p|DualFeasible γ p.1 p.2}
def dualBox (γ:Fin n→ℝ) : Set (DualPoint n) := Icc (0,0) (1,fun _ j=>γ j)

theorem dual_set_closed (γ:Fin n→ℝ) : IsClosed (dualSet γ) := by
  have h1 : IsClosed {p:DualPoint n | ∀i,γ i≤p.1*γ i+∑j,p.2 i j} := by
    simp only [ofPred_forall]
    exact isClosed_iInter (fun i=>isClosed_le continuous_const (by fun_prop))
  have h2 : IsClosed {p:DualPoint n | ∀k j,0≤γ j-γ k+p.1*γ k-∑i∈univ.erase k,p.2 i j} := by
    simp only [ofPred_forall]
    exact isClosed_iInter (fun k=>isClosed_iInter (fun j=>isClosed_le continuous_const (by fun_prop)))
  have h3 : IsClosed {p:DualPoint n | ∀j,(∑i,p.2 i j)≤γ j} := by
    simp only [ofPred_forall]
    exact isClosed_iInter (fun j=>isClosed_le (by fun_prop) continuous_const)
  have h4 : IsClosed {p:DualPoint n | ∀i j,0≤p.2 i j} := by
    simp only [ofPred_forall]
    exact isClosed_iInter (fun i=>isClosed_iInter (fun j=>isClosed_le continuous_const (by fun_prop)))
  exact h1.inter (h2.inter (h3.inter h4))

theorem dual_coordinate_bound (γ:Fin n→ℝ) (s:ℝ) (lam:Fin n→Fin n→ℝ)
    (hd:DualFeasible γ s lam) (i j:Fin n) : lam i j≤γ j := by
  exact (single_le_sum (fun k (_:k∈(univ:Finset (Fin n)))=>hd.2.2.2 k j) (mem_univ i)).trans (hd.2.2.1 j)

theorem dual_attained (hn:0<n) (γ:Fin n→ℝ) (hγ:∀i,0<γ i) :
    ∃lam:Fin n→Fin n→ℝ,DualFeasible γ (dualValue γ) lam := by
  have hunit : (1,(fun _ _=>0))∈dualSet γ∩dualBox γ := by
    refine ⟨unit_dual γ (fun i=>(hγ i).le),?_⟩
    exact ⟨⟨zero_le_one,fun _ _=>le_rfl⟩,⟨le_rfl,fun _ j=>(hγ j).le⟩⟩
  have hc : IsCompact (dualSet γ∩dualBox γ):=isCompact_Icc.inter_left (dual_set_closed γ)
  obtain ⟨p,hp,hmin⟩:=hc.exists_isMinOn ⟨_,hunit⟩ continuous_fst.continuousOn
  have hpd : DualFeasible γ p.1 p.2:=hp.1
  have hval : p.1=dualValue γ := by
    apply le_antisymm
    · change p.1 ≤ sInf {s | ∃lam:Fin n→Fin n→ℝ,DualFeasible γ s lam}
      apply le_csInf
      · exact ⟨1,_,unit_dual γ (fun i=>(hγ i).le)⟩
      rintro s ⟨lam,hd⟩
      by_cases hs:s≤1
      · have hmem : (s,lam)∈dualSet γ∩dualBox γ := by
          refine ⟨hd,?_⟩
          exact ⟨⟨dual_objective_nonneg hn γ hγ s lam hd,hd.2.2.2⟩,
            ⟨hs,dual_coordinate_bound γ s lam hd⟩⟩
        exact hmin hmem
      · exact (hmin hunit).trans (le_of_not_ge hs)
    · exact dual_value_le_certificate hn γ hγ p.1 p.2 hpd
  exact ⟨p.2,hval ▸ hpd⟩
end Queelius.ProviderGuarantee

end

section
noncomputable section
open Finset
namespace Queelius.ProviderGuarantee
open ProviderGuarantee.Bound

theorem primal_le_value {n : ℕ} (γ x y : Fin n→ℝ) (w : Fin n→Fin n→ℝ)
    (hγ : ∀ i,0≤γ i) (hf : PrimalFeasible γ x y w) : primalObj γ x y w≤lpValue γ := by
  apply le_csSup
  · refine ⟨1,?_⟩
    rintro z ⟨a,b,c,h,rfl⟩
    exact primal_objective_le_one γ a b c hγ h
  · exact ⟨x,y,w,hf,rfl⟩

theorem single_edge_primal {n : ℕ} (γ : Fin n→ℝ) (i j : Fin n) (hi : 0<γ i) :
    PrimalFeasible γ (fun _=>0) (fun _=>0)
      (fun k l=>if k=i ∧ l=j then (γ i)⁻¹ else 0) ∧
    primalObj γ (fun _=>0) (fun _=>0)
      (fun k l=>if k=i ∧ l=j then (γ i)⁻¹ else 0)=(γ i-γ j)/γ i := by
  classical
  have hs (l : Fin n) : (∑ k,if k=i ∧ l=j then (γ i)⁻¹ else 0)=if l=j then (γ i)⁻¹ else 0 := by
    by_cases h:l=j <;> simp [h]
  constructor
  · refine ⟨?_,?_,?_,?_,?_⟩
    · simp [ite_and,mul_ite,ite_mul,hi.ne']
    · intro k l
      rw [hs]
      by_cases h:l=j <;> by_cases hk:k=i <;> simp [h,hk,inv_nonneg.mpr hi.le]
    · intro k;rfl
    · intro k;rfl
    · intro k l;dsimp only;split <;> positivity
  · simp [primalObj,ite_and,ite_mul,div_eq_mul_inv,mul_comm]

theorem fan_primal {n : ℕ} (γ : Fin n→ℝ) (i : Fin n) (c : ℝ)
    (hc : 0≤c) (hnorm : c*((∑ k,γ k)+((n:ℝ)-1)*γ i)=1) :
    PrimalFeasible γ (fun k=>if k=i then 0 else c) (fun _=>0)
      (fun k _=>if k=i then c else 0) ∧
    primalObj γ (fun k=>if k=i then 0 else c) (fun _=>0)
      (fun k _=>if k=i then c else 0)=((n:ℝ)-1)*γ i*c := by
  classical
  have hx : (∑ k,γ k*(if k=i then 0 else c))=((∑ k,γ k)-γ i)*c := by
    calc
      _ = ∑ k, (γ k*c-(if k=i then γ i*c else 0)) := by
        apply sum_congr rfl
        intro k _
        by_cases h:k=i <;> simp [h]
      _ = _ := by simp [sum_sub_distrib,←sum_mul] <;> ring
  have hw : (∑ k,∑ l : Fin n,(if k=i then c else 0)*γ k)=(n:ℝ)*c*γ i := by simp [ite_mul];ring
  have hf : PrimalFeasible γ (fun k=>if k=i then 0 else c) (fun _=>0)
      (fun k _=>if k=i then c else 0) := by
    refine ⟨?_,?_,?_,?_,?_⟩
    · rw [hx,hw];nlinarith [hnorm]
    · intro k l
      simp only [sum_ite_eq',mem_univ,ite_true,sub_zero]
      by_cases h:k=i <;> simp [h]
    · intro k;dsimp only;split <;> positivity
    · intro k;rfl
    · intro k l;dsimp only;split <;> positivity
  refine ⟨hf,?_⟩
  rw [primal_objective_identity γ _ _ _ hf]
  have hcol : (∑ k,∑ l,(if k=i then c else 0)*γ l)=c*∑ l,γ l := by simp [ite_mul,mul_sum]
  simp only [mul_zero,sum_const_zero,sub_zero]
  rw [hcol]
  nlinarith [hnorm]
end Queelius.ProviderGuarantee

end

section
noncomputable section
open Finset
namespace Queelius.ProviderGuarantee.Controls
open ProviderGuarantee.Bound

theorem empty_providers_infeasible (γ x y : Fin 0 → ℝ) (w : Fin 0 → Fin 0 → ℝ) :
    ¬PrimalFeasible γ x y w := by
  intro h
  simpa using h.1

theorem zero_weights_infeasible {n : ℕ} (x y : Fin n → ℝ) (w : Fin n → Fin n → ℝ) :
    ¬PrimalFeasible (fun _=>0) x y w := by
  intro h
  simpa using h.1

theorem one_provider_dual (g : ℝ) (hg : 0≤g) :
    DualFeasible (fun _ : Fin 1=>g) 0 (fun _ _=>g) := by
  simpa [DualFeasible] using hg

theorem one_provider_values_zero (g : ℝ) (hg : 0<g) :
    lpValue (fun _ : Fin 1=>g)=0 ∧ dualValue (fun _ : Fin 1=>g)=0 := by
  have hp:=(well_posed (by decide) (fun _ : Fin 1=>g) (fun _=>hg)).2.2.1
  have hd:=one_provider_dual g hg.le
  have hb:=dual_value_bounds (by decide) (fun _ : Fin 1=>g) (fun _=>hg)
  exact ⟨le_antisymm (lp_le_dual_certificate (by decide) _ (fun _=>hg) 0 _ hd) hp,
    le_antisymm (dual_value_le_certificate (by decide) _ (fun _=>hg) 0 _ hd) hb.1⟩

theorem negative_primal_objective :
    PrimalFeasible (fun _ : Fin 1=>(1:ℝ)) (fun _=>1) (fun _=>2) (fun _ _=>0) ∧
    primalObj (fun _ : Fin 1=>(1:ℝ)) (fun _=>1) (fun _=>2) (fun _ _=>0)= -1 := by
  norm_num [PrimalFeasible,primalObj]

theorem signed_weights_feasible (t : ℝ) (ht : 1≤t) :
    PrimalFeasible ![1,-1] ![1,0] ![1,t] (fun _ _=>0) := by
  simp only [PrimalFeasible,Fin.sum_univ_two,Fin.forall_fin_two,
    Matrix.cons_val_zero,Matrix.cons_val_one,zero_mul,mul_zero,mul_one,one_mul,
    neg_mul,zero_add,add_zero,sub_self,sub_zero]
  constructor
  · norm_num
  · constructor
    · constructor <;> constructor <;> linarith
    · norm_num
      exact le_trans (by norm_num) ht

theorem signed_weights_objective (t : ℝ) :
    primalObj ![1,-1] ![1,0] ![1,t] (fun _ _=>0)=t := by
  norm_num [primalObj,Fin.sum_univ_two]

theorem positivity_is_needed_for_boundedness (M : ℝ) :
    ∃ x y : Fin 2 → ℝ,∃ w : Fin 2 → Fin 2 → ℝ,
      PrimalFeasible ![1,-1] x y w ∧ M<primalObj ![1,-1] x y w := by
  refine ⟨![1,0],![1,max 1 (M+1)],fun _ _=>0,signed_weights_feasible _ (le_max_left _ _),?_⟩
  rw [signed_weights_objective]
  exact lt_of_lt_of_le (by linarith) (le_max_right _ _)

theorem interior_peak_not_quasiconvex :
    ¬QuasiconvexOn ℝ (Set.Icc (fun _ : Fin 1=>(-1:ℝ)) (fun _=>1))
      (fun x=> -(x 0)^2) := by
  intro hf
  obtain ⟨y,hy,he,hfval⟩:=box_vertex _ _ _ hf (fun _=>0) ⟨by intro i;norm_num,by intro i;norm_num⟩
  rcases he 0 with h|h
  · simp only [h] at hfval
    norm_num at hfval
  · simp only [h] at hfval
    norm_num at hfval
end Queelius.ProviderGuarantee.Controls

end

section
noncomputable section
open Finset
namespace Queelius.ProviderGuarantee
open ProviderGuarantee.Bound

theorem dual_scale {n : ℕ} (γ : Fin n→ℝ) (s b : ℝ) (hb : 0≤b)
    (lam : Fin n→Fin n→ℝ) (h : DualFeasible γ s lam) :
    DualFeasible (fun i=>b*γ i) s (fun i j=>b*lam i j) := by
  refine ⟨?_,?_,?_,?_⟩
  · intro i
    have hh:=mul_le_mul_of_nonneg_left (h.1 i) hb
    simpa only [mul_add,mul_sum,mul_assoc,mul_comm,mul_left_comm] using hh
  · intro k j
    have hh:=mul_nonneg hb (h.2.1 k j)
    simpa only [mul_add,mul_sub,mul_sum,mul_assoc,mul_comm,mul_left_comm] using hh
  · intro j
    simpa only [mul_sum] using mul_le_mul_of_nonneg_left (h.2.2.1 j) hb
  · intro i j
    exact mul_nonneg hb (h.2.2.2 i j)

theorem vertex_normalization (n m : ℕ) (a b : ℝ) (hb : b≠0) :
    vertexProfile n m a b=fun i=>b*vertexProfile n m (1-heterogeneity a b) 1 i := by
  funext i
  dsimp [vertexProfile,heterogeneity]
  by_cases h:(i:ℕ) < m <;> simp only [h,if_true,if_false,mul_one]
  field_simp
  <;> ring

theorem singleton_lp (γ : Fin 1→ℝ) (hγ : ∀ i,0<γ i) : lpValue γ=0 := by
  have hd : DualFeasible γ 0 (fun _ j=>γ j) := by
    refine ⟨?_,?_,?_,?_⟩
    · intro i
      have hi : i=0:=Fin.eq_zero i
      subst i
      simp
    · intro k j
      have hk : k=0:=Fin.eq_zero k
      have hj : j=0:=Fin.eq_zero j
      subst k;subst j
      simp
    · intro j;simp
    · intro i j;exact (hγ j).le
  exact le_antisymm (lp_le_dual_certificate (by norm_num) γ hγ 0 _ hd) (well_posed (by norm_num) γ hγ).2.2.1
end Queelius.ProviderGuarantee

end

section
noncomputable section
open Finset
namespace Queelius.ProviderGuarantee
open ProviderGuarantee.Bound

-- Abstract certificate conditions isolate finite summation from scalar algebra.
theorem vertex_dual_certificate (n m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ n)
    (a b s t : ℝ) (hab : a ≤ b) (hs : s ≤ 1) (ht : 0 ≤ t)
    (hlam : 0 ≤ (1-s)*a-((n:ℝ)-m)*t)
    (hcol : (n:ℝ)*t ≤ a)
    (hlow : ((n:ℝ)-1)*t ≤ a-(1-s)*b)
    (hhigh : (1-s)*((m:ℝ)*b+((n:ℝ)-m)*a+((m:ℝ)-1)*b)
      -((n:ℝ)-1)*((n:ℝ)-m)*t ≤ (m:ℝ)*b) :
    DualFeasible (vertexProfile n m a b) s
      (fun i j => if (j:ℕ) < m then
        ((1-s)*vertexProfile n m a b i-((n:ℝ)-m)*t)/m else t) := by
  have hmR : (1:ℝ) ≤ m:=by exact_mod_cast hm
  have hm0 : (0:ℝ) < m:=by linarith
  have hnm : (m:ℝ) ≤ n:=by exact_mod_cast hmn
  let γ := vertexProfile n m a b
  let lam := fun i j : Fin n=>if (j:ℕ) < m then ((1-s)*γ i-((n:ℝ)-m)*t)/m else t
  let C : ℝ := ((1-s)*((m:ℝ)*b+((n:ℝ)-m)*a)-(n:ℝ)*((n:ℝ)-m)*t)/m
  have hrow (i : Fin n) : (∑ j,lam i j)=(1-s)*γ i := by
    dsimp [lam]
    rw [vertex_sum n m hmn]
    field_simp [hm0.ne']
    <;> ring
  have hsum : (∑ i,γ i)=(m:ℝ)*b+((n:ℝ)-m)*a := vertex_sum n m hmn a b
  have hcolumn (j : Fin n) : (∑ i,lam i j)=if (j:ℕ) < m then C else (n:ℝ)*t := by
    by_cases hj:(j:ℕ) < m
    · dsimp [lam]
      simp only [if_pos hj]
      rw [←sum_div]
      simp only [sum_sub_distrib,←mul_sum,sum_const,nsmul_eq_mul,Fintype.card_fin,card_univ,hsum]
      dsimp [C];ring
    · simp [lam,hj]
  have hnonneg (i j : Fin n) : 0 ≤ lam i j := by
    dsimp [lam]
    split
    · apply div_nonneg _ hm0.le
      have hi:=(vertex_weight_bounds n m a b hab i).1
      have hh:=mul_le_mul_of_nonneg_left hi (show 0 ≤ 1-s by linarith)
      change (1-s)*a ≤ (1-s)*γ i at hh
      linarith
    · exact ht
  have hsecond (k j : Fin n) : 0 ≤ γ j-γ k+s*γ k-∑ i ∈ univ.erase k,lam i j := by
    have herase:=sum_erase_add univ (fun i=>lam i j) (mem_univ k)
    rw [hcolumn] at herase
    by_cases hj:(j:ℕ) < m
    · simp only [if_pos hj] at herase
      have hγj : γ j=b:=by simp [γ,vertexProfile,hj]
      have hlamk : (m:ℝ)*lam k j=(1-s)*γ k-((n:ℝ)-m)*t := by
        dsimp [lam];rw [if_pos hj];field_simp
      have hC : (m:ℝ)*C=(1-s)*((m:ℝ)*b+((n:ℝ)-m)*a)-(n:ℝ)*((n:ℝ)-m)*t := by dsimp [C];field_simp
      have hk:=(vertex_weight_bounds n m a b hab k).2
      change γ k ≤ b at hk
      have hmulk:=mul_le_mul_of_nonneg_left hk (mul_nonneg (show 0 ≤ 1-s by linarith) (show 0 ≤ (m:ℝ)-1 by linarith))
      rw [hγj]
      apply (mul_nonneg_iff_of_pos_left hm0).mp
      nlinarith [hhigh]
    · simp only [if_neg hj] at herase
      have hγj : γ j=a:=by simp [γ,vertexProfile,hj]
      have hlamk : lam k j=t:=by simp [lam,hj]
      rw [hlamk] at herase
      have hk:=(vertex_weight_bounds n m a b hab k).2
      have hh:=mul_le_mul_of_nonneg_left hk (show 0 ≤ 1-s by linarith)
      change (1-s)*γ k ≤ (1-s)*b at hh
      rw [hγj]
      nlinarith [hlow]
  change DualFeasible γ s lam
  refine ⟨?_,hsecond,?_,hnonneg⟩
  · intro i;rw [hrow];nlinarith
  · intro j
    rw [hcolumn]
    by_cases hj:(j:ℕ) < m
    · rw [if_pos hj]
      have hγj : γ j=b:=by simp [γ,vertexProfile,hj]
      rw [hγj]
      have hγ0 : a ≤ b:=hab
      have hL : 0 ≤ (1-s)*b-((n:ℝ)-m)*t := by nlinarith [mul_nonneg (show 0 ≤ 1-s by linarith) (sub_nonneg.mpr hab)]
      have hC : (m:ℝ)*C=(1-s)*((m:ℝ)*b+((n:ℝ)-m)*a)-(n:ℝ)*((n:ℝ)-m)*t := by dsimp [C];field_simp
      apply (mul_le_mul_iff_right₀ hm0).mp
      have hlt := mul_nonneg (sub_nonneg.mpr hnm) ht
      have hbprod : 0 ≤ (1-s)*b:=by linarith
      nlinarith [mul_nonneg (show 0 ≤ (m:ℝ)-1 by linarith) hbprod]
    · simpa [hj,γ,vertexProfile] using hcol
end Queelius.ProviderGuarantee

end

section
noncomputable section
open Finset Classical
namespace Queelius.ProviderGuarantee
open ProviderGuarantee.Bound
variable {n : ℕ}

theorem lp_nonneg_all_dimensions (γ : Fin n → ℝ) (hγ : ∀ i,0 < γ i) : 0 ≤ lpValue γ := by
  by_cases hn : 0 < n
  · exact (well_posed hn γ hγ).2.2.1
  · have hn0 : n=0 := by omega
    subst n
    simp [lpValue,PrimalFeasible]

theorem normalized_primal (γ x y : Fin n → ℝ) (w : Fin n → Fin n → ℝ) (Z : ℝ)
    (hZ : 0 < Z) (hden : (∑ i,γ i*x i)+(∑ i,∑ j,w i j*γ i)=Z)
    (hcon : ∀ i j,x i ≤ (∑ k,w k j)-w i j+y j)
    (hx : ∀ i,0≤x i) (hy : ∀ i,0≤y i) (hw : ∀ i j,0≤w i j) :
    PrimalFeasible γ (fun i=>x i/Z) (fun i=>y i/Z) (fun i j=>w i j/Z) := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · simp only [div_mul_eq_mul_div,←mul_div_assoc,←sum_div,←add_div]
    rw [hden,div_self hZ.ne']
  · intro i j
    rw [←sum_div,←add_div,←sub_div,←sub_div]
    apply div_nonpos_of_nonpos_of_nonneg _ hZ.le
    linarith [hcon i j]
  · intro i
    exact div_nonneg (hx i) hZ.le
  · intro i
    exact div_nonneg (hy i) hZ.le
  · intro i j
    exact div_nonneg (hw i j) hZ.le

theorem normalized_objective (γ x y : Fin n → ℝ) (w : Fin n → Fin n → ℝ) (Z : ℝ) :
    primalObj γ (fun i=>x i/Z) (fun i=>y i/Z) (fun i j=>w i j/Z)=primalObj γ x y w/Z := by
  simp only [primalObj,div_mul_eq_mul_div,←mul_div_assoc,←sum_div,←sub_div,←add_div]

theorem fractional_le_lp (γ x y : Fin n → ℝ) (w : Fin n → Fin n → ℝ)
    (hγ : ∀ i,0 < γ i) (hcon : ∀ i j,x i ≤ (∑ k,w k j)-w i j+y j)
    (hx : ∀ i,0≤x i) (hy : ∀ i,0≤y i) (hw : ∀ i j,0≤w i j) :
    primalObj γ x y w/((∑ i,γ i*x i)+(∑ i,∑ j,w i j*γ i)) ≤ lpValue γ := by
  let Z : ℝ := (∑ i,γ i*x i)+(∑ i,∑ j,w i j*γ i)
  have hZ0 : 0≤Z := add_nonneg (sum_nonneg (fun i _=>mul_nonneg (hγ i).le (hx i)))
    (sum_nonneg (fun i _=>sum_nonneg (fun j _=>mul_nonneg (hw i j) (hγ i).le)))
  change primalObj γ x y w/Z ≤ lpValue γ
  by_cases hZ : Z=0
  · rw [hZ,div_zero]
    exact lp_nonneg_all_dimensions γ hγ
  · have hZp : 0 < Z := lt_of_le_of_ne hZ0 (Ne.symm hZ)
    have hf:=normalized_primal γ x y w Z hZp rfl hcon hx hy hw
    have hb : BddAbove {z | ∃ x y : Fin n → ℝ,∃ w : Fin n → Fin n → ℝ,
        PrimalFeasible γ x y w ∧ z=primalObj γ x y w} := by
      refine ⟨1,?_⟩
      rintro z ⟨a,b,c,h,rfl⟩
      exact primal_objective_le_one γ a b c (fun i=>(hγ i).le) h
    have h:=le_csSup hb (show primalObj γ (fun i=>x i/Z) (fun i=>y i/Z) (fun i j=>w i j/Z)∈
        {z | ∃ x y : Fin n → ℝ,∃ w : Fin n → Fin n → ℝ,PrimalFeasible γ x y w ∧ z=primalObj γ x y w}
        from ⟨_,_,_,hf,rfl⟩)
    rw [normalized_objective] at h
    exact h

variable {D : Type*} [Fintype D] [DecidableEq D]

theorem optimal_exists (γ : Fin n → ℝ) (v : D → ℝ)
    (F : Set (Fin n → Finset D)) (hF : F.Nonempty) : ∃ A,IsOptimal γ v F A := by
  let T : Finset (Fin n → Finset D) := univ.filter (fun A=>A∈F)
  have hT : T.Nonempty := by obtain ⟨A,hA⟩:=hF;exact ⟨A,by simpa [T] using hA⟩
  obtain ⟨A,hA,hmax⟩:=exists_max_image T (totalValue γ v) hT
  refine ⟨A,by simpa [T] using hA,?_⟩
  intro B hB
  exact hmax B (by simpa [T] using hB)

theorem allocation_loss_le_lp (v : D → ℝ) (γ : Fin n → ℝ) (hγ : ∀ i,0 < γ i)
    (F FG : Set (Fin n → Finset D)) (h1 : Assumption1 F) (h2 : Assumption2 v F FG)
    (hFG : FG.Nonempty) : valueLoss γ v F FG ≤ lpValue γ := by
  obtain ⟨A,hA⟩:=optimal_exists γ v F (hFG.mono h2.1)
  obtain ⟨B,hB⟩:=optimal_exists γ v FG hFG
  have h:=allocation_scalar_reduction v γ hγ F FG h1 h2 A B hA hB
  dsimp only at h
  rw [h.2.2.2.2.2.2]
  exact fractional_le_lp γ _ _ _ hγ h.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2.1
end Queelius.ProviderGuarantee

end

section
noncomputable section
open Finset Classical
namespace Queelius.ProviderGuarantee
open ProviderGuarantee.Bound
variable {n : ℕ}

theorem dual_near_certificate (γ : Fin n → ℝ) (hγ : ∀ i,0≤γ i) (t : ℝ)
    (ht : dualValue γ < t) : ∃ lam,DualFeasible γ t lam := by
  have hn : {s | ∃ lam : Fin n → Fin n → ℝ,DualFeasible γ s lam}.Nonempty :=
    ⟨1,_,unit_dual γ hγ⟩
  obtain ⟨s,⟨lam,h⟩,hst⟩:=exists_lt_of_csInf_lt hn ht
  exact ⟨lam,dual_certificate_raise γ hγ s t hst.le lam h⟩

theorem dual_value_zero_dimension (γ : Fin 0 → ℝ) : dualValue γ=0 := by
  simp [dualValue,DualFeasible]

theorem dual_box_quasiconvex (γmin γmax : ℝ) (hγmin : 0 < γmin) :
    QuasiconvexOn ℝ (Set.Icc (fun _ : Fin n=>γmin) (fun _=>γmax)) dualValue := by
  apply quasiconvexOn_iff_le_max.mpr
  refine ⟨convex_Icc _ _,?_⟩
  intro γ hγ η hη a b ha hb hab
  by_cases hn : 0 < n
  · have hg : ∀ i,0 < γ i:=fun i=>lt_of_lt_of_le hγmin (hγ.1 i)
    have hh : ∀ i,0 < η i:=fun i=>lt_of_lt_of_le hγmin (hη.1 i)
    have hm : a • γ+b • η∈Set.Icc (fun _=>γmin) (fun _=>γmax) :=
      (convex_Icc _ _) hγ hη ha hb hab
    have hp : ∀ i,0 < (a • γ+b • η) i:=fun i=>lt_of_lt_of_le hγmin (hm.1 i)
    apply le_of_forall_pos_le_add
    intro ε hε
    let t:=max (dualValue γ) (dualValue η)+ε
    have htγ : dualValue γ < t:=lt_add_of_le_of_pos (le_max_left _ _) hε
    have htη : dualValue η < t:=lt_add_of_le_of_pos (le_max_right _ _) hε
    obtain ⟨lam,hl⟩:=dual_near_certificate γ (fun i=>(hg i).le) t htγ
    obtain ⟨mu,hu⟩:=dual_near_certificate η (fun i=>(hh i).le) t htη
    exact dual_value_le_certificate hn _ hp t _ (fixed_value_dual_mix γ η t a b ha hb lam mu hl hu)
  · have hn0 : n=0 := by omega
    subst n
    simp only [dual_value_zero_dimension,max_self,le_refl]

theorem dual_box_all (γmin γmax : ℝ) (hγmin : 0 < γmin) :
    QuasiconvexOn ℝ (Set.Icc (fun _ : Fin n=>γmin) (fun _=>γmax)) dualValue ∧
    ∀ γ∈Set.Icc (fun _ : Fin n=>γmin) (fun _=>γmax),0≤dualValue γ ∧ dualValue γ≤1 := by
  refine ⟨dual_box_quasiconvex γmin γmax hγmin,?_⟩
  intro γ hγ
  by_cases hn : 0 < n
  · have h:=dual_value_bounds hn γ (fun i=>lt_of_lt_of_le hγmin (hγ.1 i))
    exact ⟨h.1,h.2.1⟩
  · have hn0 : n=0 := by omega
    subst n
    simp [dual_value_zero_dimension]
end Queelius.ProviderGuarantee

end

section
noncomputable section
namespace Queelius.ProviderGuarantee.Controls
open ProviderGuarantee.Bound

theorem unbounded_primal_slack (T : ℝ) (hT : 1 ≤ T) :
    PrimalFeasible (fun _ : Fin 1 => 1) (fun _ => 1) (fun _ => T) (fun _ _ => 0) ∧
    primalObj (fun _ : Fin 1 => 1) (fun _ => 1) (fun _ => T) (fun _ _ => 0) = 1-T := by
  constructor
  · simp [PrimalFeasible, show (0:ℝ) ≤ T by linarith,
      show (1:ℝ)-T ≤ 0 by linarith]
  · simp [primalObj]

theorem clipping_strictly_improves (T : ℝ) (hT : 1 < T) :
    PrimalFeasible (fun _ : Fin 1 => 1) (fun _ => 1)
      (fun _ => min T 1) (fun _ _ => 0) ∧
    primalObj (fun _ : Fin 1 => 1) (fun _ => 1) (fun _ => T) (fun _ _ => 0) <
      primalObj (fun _ : Fin 1 => 1) (fun _ => 1) (fun _ => min T 1) (fun _ _ => 0) := by
  have hc := clamp_primal (fun _ : Fin 1 => (1:ℝ)) (fun _ => 1) (fun _ => T)
    (fun _ _ => 0) 1 (by intro; norm_num) (by norm_num) (by intro; rfl)
    (unbounded_primal_slack T hT.le).1
  refine ⟨hc.1, ?_⟩
  simp [primalObj, min_eq_right hT.le]
  linarith

theorem singleton_dual_boundary :
    DualFeasible (fun _ : Fin 1 => 1) 0 (fun _ _ => 1) ∧
    (0,(fun _ _ => (1:ℝ))) ∈ dualBox (fun _ : Fin 1 => 1) := by
  constructor
  · norm_num [DualFeasible, Fin.sum_univ_one]
  · exact ⟨⟨le_rfl,fun _ _ => zero_le_one⟩,⟨zero_le_one,fun _ _ => le_rfl⟩⟩

theorem singleton_dual_value : dualValue (fun _ : Fin 1 => 1) = 0 := by
  exact le_antisymm
    (dual_value_le_certificate (by norm_num) _ (by intro; norm_num) _ _ singleton_dual_boundary.1)
    (dual_value_bounds (by norm_num) _ (by intro; norm_num)).1

end Queelius.ProviderGuarantee.Controls

end

section
noncomputable section
open Finset Matrix
namespace Queelius.ProviderGuarantee
open ProviderGuarantee.Bound
variable {n : ℕ}

abbrev LPRow (n : ℕ) := Option (Fin n × Fin n)
abbrev LPCol (n : ℕ) := Fin n ⊕ (Fin n ⊕ ((Fin n × Fin n) ⊕ (Fin n × Fin n)))

def stdMatrix (γ : Fin n → ℝ) : Matrix (LPRow n) (LPCol n) ℝ
  | none, .inl i => γ i
  | none, .inr (.inl _) => 0
  | none, .inr (.inr (.inl ij)) => γ ij.1
  | none, .inr (.inr (.inr _)) => 0
  | some ij, .inl k => if k = ij.1 then 1 else 0
  | some ij, .inr (.inl k) => if k = ij.2 then -1 else 0
  | some ij, .inr (.inr (.inl kl)) =>
      (if kl = ij then 1 else 0) - (if kl.2 = ij.2 then 1 else 0)
  | some ij, .inr (.inr (.inr kl)) => if kl = ij then 1 else 0

def stdCost (γ : Fin n → ℝ) : LPCol n → ℝ
  | .inl i => -γ i
  | .inr (.inl i) => γ i
  | .inr (.inr (.inl ij)) => γ ij.2 - γ ij.1
  | .inr (.inr (.inr _)) => 0

def stdRhs : LPRow n → ℝ | none => 1 | some _ => 0

def encodePrimal (x y : Fin n → ℝ) (w z : Fin n → Fin n → ℝ) : LPCol n → ℝ
  | .inl i => x i
  | .inr (.inl i) => y i
  | .inr (.inr (.inl ij)) => w ij.1 ij.2
  | .inr (.inr (.inr ij)) => z ij.1 ij.2

theorem std_normalization (γ : Fin n → ℝ) (u : LPCol n → ℝ) :
    (∑ c, stdMatrix γ none c * u c) =
      (∑ i, γ i * u (.inl i)) + ∑ i, ∑ j, u (.inr (.inr (.inl (i,j)))) * γ i := by
  simp [Fintype.sum_sum_type, Fintype.sum_prod_type, stdMatrix, mul_comm]

theorem std_constraint (γ : Fin n → ℝ) (u : LPCol n → ℝ) (i j : Fin n) :
    (∑ c, stdMatrix γ (some (i,j)) c * u c) =
      u (.inl i) + u (.inr (.inr (.inl (i,j)))) -
        (∑ k, u (.inr (.inr (.inl (k,j))))) - u (.inr (.inl j)) +
          u (.inr (.inr (.inr (i,j)))) := by
  simp [Fintype.sum_sum_type, Fintype.sum_prod_type, stdMatrix, sub_mul,
    sum_sub_distrib, ite_mul, Prod.mk.injEq, and_comm]
  ring

theorem std_objective (γ : Fin n → ℝ) (u : LPCol n → ℝ) :
    (∑ c, stdCost γ c * u c) = -primalObj γ (fun i => u (.inl i))
      (fun i => u (.inr (.inl i))) (fun i j => u (.inr (.inr (.inl (i,j))))) := by
  simp only [Fintype.sum_sum_type,Fintype.sum_prod_type,stdCost,zero_mul,sum_const_zero,
    neg_mul,sub_mul,sum_sub_distrib,sum_neg_distrib,primalObj,mul_sub]
  simp only [mul_comm]
  ring

theorem std_dual_x (γ : Fin n → ℝ) (p : LPRow n → ℝ) (i : Fin n) :
    (∑ r, stdMatrix γ r (.inl i) * p r) = γ i * p none + ∑ j, p (some (i,j)) := by
  simp [Fintype.sum_option,Fintype.sum_prod_type,stdMatrix,ite_mul,eq_comm,
    Finset.sum_ite_irrel]
  rw [sum_comm]
  simp

theorem std_dual_y (γ : Fin n → ℝ) (p : LPRow n → ℝ) (j : Fin n) :
    (∑ r, stdMatrix γ r (.inr (.inl j)) * p r) = -(∑ i, p (some (i,j))) := by
  simp [Fintype.sum_option,Fintype.sum_prod_type,stdMatrix,ite_mul,eq_comm]

theorem std_dual_w (γ : Fin n → ℝ) (p : LPRow n → ℝ) (k j : Fin n) :
    (∑ r, stdMatrix γ r (.inr (.inr (.inl (k,j)))) * p r) =
      γ k * p none + p (some (k,j)) - ∑ i, p (some (i,j)) := by
  simp [Fintype.sum_option,Fintype.sum_prod_type,stdMatrix,ite_mul,eq_comm,
    sub_mul,sum_sub_distrib,Prod.mk.injEq]
  ring

theorem std_dual_z (γ : Fin n → ℝ) (p : LPRow n → ℝ) (i j : Fin n) :
    (∑ r, stdMatrix γ r (.inr (.inr (.inr (i,j)))) * p r) = p (some (i,j)) := by
  simp [Fintype.sum_option,Fintype.sum_prod_type,stdMatrix,ite_mul,eq_comm,Prod.mk.injEq]

theorem std_dual_objective (p : LPRow n → ℝ) : (∑ r, stdRhs r * p r) = p none := by
  simp [Fintype.sum_option,stdRhs]

end Queelius.ProviderGuarantee

end

section
noncomputable section
open Finset
namespace Queelius.ProviderGuarantee
open ProviderGuarantee.Bound

theorem vertex_scalar_parameters (N M d : ℝ) (hN : 1 < N) (hM : 1 ≤ M)
    (hMN : M ≤ N) (hd0 : 0 ≤ d) (hd1 : d < 1) :
    let Q := N+M+(1-d)*(N-M)-1
    let r := (N-1)/Q
    0 < Q ∧ 0 ≤ r ∧ r < 1 ∧ r*Q=N-1 ∧ N*r ≤ N-1 ∧ r*(2-d) ≤ 1 := by
  dsimp only
  let Q := N+M+(1-d)*(N-M)-1
  let r := (N-1)/Q
  have hQN : N ≤ Q := by dsimp [Q];nlinarith [mul_nonneg (show 0≤1-d by linarith) (sub_nonneg.mpr hMN)]
  have hQ : 0 < Q:=by linarith
  have hr0 : 0 ≤ r:=div_nonneg (by linarith) hQ.le
  have hr1 : r < 1:= (div_lt_one hQ).mpr (by linarith)
  have hreq : r*Q=N-1:=by dsimp [r];field_simp
  have hNr : N*r ≤ N-1:=by nlinarith [mul_nonneg hr0 (sub_nonneg.mpr hQN)]
  have hQ2 : (N-1)*(2-d) ≤ Q := by dsimp [Q];nlinarith [mul_nonneg hd0 (show 0≤M-1 by linarith)]
  have hr2 : r*(2-d) ≤ 1 := by
    have hh:=mul_le_mul_of_nonneg_left hQ2 hr0
    rw [hreq] at hh
    nlinarith
  exact ⟨hQ,hr0,hr1,hreq,hNr,hr2⟩

theorem vertex_dual_normalized (n m : ℕ) (hn : 1 < n) (hm : 1 ≤ m) (hmn : m ≤ n)
    (d : ℝ) (hd0 : 0 ≤ d) (hd1 : d < 1) :
    ∃ lam, DualFeasible (vertexProfile n m (1-d) 1)
      (lemma2Value n m d) lam := by
  have hnR : (1:ℝ) < n:=by exact_mod_cast hn
  have hmR : (1:ℝ) ≤ m:=by exact_mod_cast hm
  have hmnR : (m:ℝ) ≤ n:=by exact_mod_cast hmn
  let Q : ℝ := (n:ℝ)+m+(1-d)*((n:ℝ)-m)-1
  let r : ℝ := ((n:ℝ)-1)/Q
  have hp:=vertex_scalar_parameters n m d hnR hmR hmnR hd0 hd1
  change 0 < Q ∧ 0 ≤ r ∧ r < 1 ∧ r*Q=(n:ℝ)-1 ∧ (n:ℝ)*r≤(n:ℝ)-1 ∧ r*(2-d)≤1 at hp
  change ∃ lam,DualFeasible _ (max d r) lam
  by_cases hdr : r ≤ d
  · rw [max_eq_left hdr]
    refine ⟨_,vertex_dual_certificate n m hm hmn (1-d) 1 d 0 (by linarith) hd1.le le_rfl ?_ ?_ ?_ ?_⟩
    · nlinarith [sq_nonneg (1-d)]
    · nlinarith
    · ring_nf;exact le_rfl
    · have hh:=mul_le_mul_of_nonneg_right hdr hp.1.le
      rw [hp.2.2.2.1] at hh
      dsimp [Q] at hh
      nlinarith
  · have hdr' : d ≤ r:=(lt_of_not_ge hdr).le
    rw [max_eq_right hdr']
    let t : ℝ := (r-d)/((n:ℝ)-1)
    have ht : 0 ≤ t:=div_nonneg (sub_nonneg.mpr hdr') (by linarith)
    have htEq : ((n:ℝ)-1)*t=r-d := by dsimp [t];field_simp [show (n:ℝ)-1≠0 by linarith]
    have hlam : 0 ≤ (1-r)*(1-d)-((n:ℝ)-m)*t := by
      have hh : ((n:ℝ)-m)*t≤r-d := by nlinarith [mul_nonneg (show 0≤(m:ℝ)-1 by linarith) ht]
      nlinarith [hp.2.2.2.2.2]
    have hcol : (n:ℝ)*t≤1-d := by nlinarith [hp.2.2.2.2.1]
    refine ⟨_,vertex_dual_certificate n m hm hmn (1-d) 1 r t (by linarith) hp.2.2.1.le ht hlam hcol ?_ ?_⟩
    · nlinarith [htEq]
    · have hreq:=hp.2.2.2.1
      dsimp [Q] at hreq
      have hmul := congrArg (fun x : ℝ => ((n:ℝ)-m)*x) htEq
      nlinarith
end Queelius.ProviderGuarantee

end

section
noncomputable section
open Finset Classical
namespace Queelius.ProviderGuarantee.Controls
open ProviderGuarantee.Bound

theorem negative_job_strictly_worsens :
    ¬IsOptimal (fun _ : Fin 1=>(1:ℝ)) ![-1,2] Set.univ (fun _=>univ) := by
  intro h
  have hh:=h.2 (fun _=>({1}:Finset (Fin 2))) (Set.mem_univ _)
  norm_num [totalValue,ProviderGuarantee.Bound.val,Fin.sum_univ_two] at hh

theorem negative_weight_can_favor_negative_job :
    IsOptimal (fun _ : Fin 1=>(-1:ℝ)) (fun _ : Fin 1=>(-1:ℝ)) Set.univ (fun _=>{0}) := by
  refine ⟨Set.mem_univ _,?_⟩
  intro A _
  have hs : A 0 ⊆ ({0}:Finset (Fin 1)) := by
    intro i _
    simp [Subsingleton.elim i (0:Fin 1)]
  rcases subset_singleton_iff.mp hs with h|h
  · norm_num [totalValue,ProviderGuarantee.Bound.val,h]
  · norm_num [totalValue,ProviderGuarantee.Bound.val,h]

theorem zero_provider_loss (v : Fin 2 → ℝ) (γ : Fin 0 → ℝ) :
    maxValue γ v Set.univ=0 ∧ valueLoss γ v Set.univ Set.univ=0 ∧ lpValue γ=0 ∧ dualValue γ=0 := by
  have he : totalValue γ v = fun _ => (0:ℝ) := by
    funext A
    simp [totalValue]
  simp [maxValue,he,valueLoss,lpValue,PrimalFeasible,dual_value_zero_dimension]

theorem all_zero_normalization_infeasible :
    ¬PrimalFeasible (fun _ : Fin 1=>(1:ℝ)) (fun _=>0/0) (fun _=>0/0) (fun _ _=>0/0) := by
  norm_num [PrimalFeasible]

theorem all_zero_job_values_loss :
    maxValue (fun _ : Fin 1=>(1:ℝ)) (fun _ : Fin 1=>(0:ℝ)) Set.univ=0 ∧
    valueLoss (fun _ : Fin 1=>(1:ℝ)) (fun _ : Fin 1=>(0:ℝ)) Set.univ Set.univ=0 := by
  have he : totalValue (fun _ : Fin 1 => (1:ℝ)) (fun _ : Fin 1 => (0:ℝ)) = fun _ => (0:ℝ) := by
    funext A
    simp [totalValue,ProviderGuarantee.Bound.val]
  simp [maxValue,he,valueLoss]

theorem dual_certificate_can_be_raised :
    DualFeasible (fun _ : Fin 1=>(1:ℝ)) 2 (fun _ _=>0) :=
  dual_certificate_raise _ (fun _=>by norm_num) 1 2 (by norm_num) _ (unit_dual _ (fun _=>by norm_num))

theorem homogeneous_vertex_expression :
    lemma2Value 2 1 (heterogeneity 1 1)=1/3 ∧
    lemma2Value 2 2 (heterogeneity 1 1)=1/3 := by
  norm_num [lemma2Value,heterogeneity]

theorem full_high_vertex_needs_correction :
    lpValue (vertexProfile 1 1 1 2)=0 ∧ lemma2Value 1 1 (heterogeneity 1 2)=1/2 := by
  constructor
  · have h:=one_provider_values_zero 2 (by norm_num)
    have he : vertexProfile 1 1 1 2 = fun _ => (2:ℝ) := by
      funext i
      fin_cases i
      norm_num [vertexProfile]
    simpa only [he] using h.1
  · norm_num [lemma2Value,heterogeneity]
end Queelius.ProviderGuarantee.Controls

end

section
noncomputable section
open Finset Matrix
namespace Queelius.ProviderGuarantee
open ProviderGuarantee.Bound
variable {n : ℕ}

theorem decode_std_primal (γ : Fin n → ℝ) (u : LPCol n → ℝ)
    (hu : ∀ c, 0 ≤ u c) (hA : ∀ r, ∑ c, stdMatrix γ r c * u c = stdRhs r) :
    PrimalFeasible γ (fun i => u (.inl i)) (fun i => u (.inr (.inl i)))
      (fun i j => u (.inr (.inr (.inl (i,j))))) := by
  refine ⟨?_,?_,fun i => hu _,fun i => hu _,fun i j => hu _⟩
  · simpa only [std_normalization,stdRhs] using hA none
  · intro i j
    have h := hA (some (i,j))
    rw [std_constraint,stdRhs] at h
    linarith [hu (.inr (.inr (.inr (i,j))))]

theorem encode_std_primal (γ x y : Fin n → ℝ) (w : Fin n → Fin n → ℝ)
    (hp : PrimalFeasible γ x y w) :
    let u := encodePrimal x y w (fun i j => y j + (∑ k, w k j) - x i - w i j)
    (∀ c, 0 ≤ u c) ∧ (∀ r, ∑ c, stdMatrix γ r c * u c = stdRhs r) := by
  dsimp only
  constructor
  · intro c
    rcases c with i | c
    · exact hp.2.2.1 i
    rcases c with i | c
    · exact hp.2.2.2.1 i
    rcases c with ij | ij
    · exact hp.2.2.2.2 ij.1 ij.2
    · change 0 ≤ y ij.2 + (∑ k, w k ij.2) - x ij.1 - w ij.1 ij.2
      linarith [hp.2.1 ij.1 ij.2]
  · intro r
    cases r with
    | none => simpa only [std_normalization,encodePrimal,stdRhs] using hp.1
    | some ij => simp only [std_constraint,encodePrimal,stdRhs]; ring

theorem decode_std_dual (γ : Fin n → ℝ) (p : LPRow n → ℝ)
    (hp : ∀ c, ∑ r, stdMatrix γ r c * p r ≤ stdCost γ c) :
    DualFeasible γ (-p none) (fun i j => -p (some (i,j))) := by
  refine ⟨?_,?_,?_,?_⟩
  · intro i
    have h := hp (.inl i)
    rw [std_dual_x,stdCost] at h
    simp only [sum_neg_distrib]
    nlinarith
  · intro k j
    have h := hp (.inr (.inr (.inl (k,j))))
    rw [std_dual_w,stdCost] at h
    have hs := sum_erase_add univ (fun i => p (some (i,j))) (mem_univ k)
    simp only [sum_neg_distrib]
    nlinarith
  · intro j
    have h := hp (.inr (.inl j))
    simpa only [std_dual_y,stdCost,sum_neg_distrib] using h
  · intro i j
    have h := hp (.inr (.inr (.inr (i,j))))
    rw [std_dual_z,stdCost] at h
    linarith

theorem duality_equality (hn : 0 < n) (γ : Fin n → ℝ) (hγ : ∀ i, 0 < γ i) :
    lpValue γ = dualValue γ := by
  obtain ⟨x,y,w,hp,hval⟩ := primal_attained hn γ hγ
  let u := encodePrimal x y w (fun i j => y j + (∑ k, w k j) - x i - w i j)
  have hu := encode_std_primal γ x y w hp
  have hobj : (∑ c, stdCost γ c * u c) = -lpValue γ := by
    simpa only [u,std_objective,encodePrimal,hval]
  have hopt (v : LPCol n → ℝ) (hv : ∀ c, 0 ≤ v c)
      (hAv : ∀ r, ∑ c, stdMatrix γ r c * v c = stdRhs r) :
      (∑ c, stdCost γ c * u c) ≤ ∑ c, stdCost γ c * v c := by
    rw [hobj,std_objective]
    exact neg_le_neg (primal_le_value γ _ _ _ (fun i => (hγ i).le)
      (decode_std_primal γ v hv hAv))
  obtain ⟨p,hpd,hpe⟩ := finite_lp_duality (stdMatrix γ) (stdCost γ) stdRhs u hu.1 hu.2 hopt
  have hd := decode_std_dual γ p hpd
  have he : -p none = lpValue γ := by
    rw [std_dual_objective,hobj] at hpe
    linarith
  exact le_antisymm (dual_value_bounds hn γ hγ).2.2
    (he ▸ dual_value_le_certificate hn γ hγ _ _ hd)

end Queelius.ProviderGuarantee

namespace ProviderGuarantee.Bound
theorem strong_duality {n : ℕ} (hn : 0 < n) (γ : Fin n → ℝ) (hγ : ∀ i, 0 < γ i) :
    (∀ (x y : Fin n → ℝ) (w : Fin n → Fin n → ℝ) (s : ℝ) (lam : Fin n → Fin n → ℝ),
      PrimalFeasible γ x y w → DualFeasible γ s lam → primalObj γ x y w ≤ s) ∧
    (∃ x y : Fin n → ℝ, ∃ w : Fin n → Fin n → ℝ,
      PrimalFeasible γ x y w ∧ primalObj γ x y w = lpValue γ) ∧
    (∃ lam : Fin n → Fin n → ℝ, DualFeasible γ (dualValue γ) lam) ∧
    lpValue γ = dualValue γ :=
  ⟨fun x y w s lam => Queelius.ProviderGuarantee.weak_duality γ x y w s lam,
    Queelius.ProviderGuarantee.primal_attained hn γ hγ,
    Queelius.ProviderGuarantee.dual_attained hn γ hγ,
    Queelius.ProviderGuarantee.duality_equality hn γ hγ⟩
end ProviderGuarantee.Bound

end

section
noncomputable section
open Finset
namespace Queelius.ProviderGuarantee
open ProviderGuarantee.Bound

theorem vertex_dual_opt_bound (n m : ℕ) (hn : 1<n) (hm : 1 ≤ m) (hmn : m≤n)
    (a b : ℝ) (ha : 0<a) (hab : a≤b) :
    ∃ lam,DualFeasible (vertexProfile n m a b) (lemma2Value n m (heterogeneity a b)) lam := by
  have hb : 0<b:=ha.trans_le hab
  have hd:=heterogeneity_range a b ha hab
  obtain ⟨lam,hl⟩:=vertex_dual_normalized n m hn hm hmn _ hd.1 hd.2
  have hscaled:=dual_scale _ _ b hb.le lam hl
  rw [←vertex_normalization n m a b hb.ne'] at hscaled
  exact ⟨_,hscaled⟩

theorem vertex_primal_floor (n m : ℕ) (hn : 1<n) (hm : 1 ≤ m) (hmn : m≤n)
    (a b : ℝ) (ha : 0<a) (hab : a≤b) :
    ((n:ℝ)-1)/((n:ℝ)+m+(1-heterogeneity a b)*((n:ℝ)-m)-1)
      ≤lpValue (vertexProfile n m a b) := by
  have hb : 0<b:=ha.trans_le hab
  have hn0 : 0<n:=by omega
  have hnR : (1:ℝ)<n:=by exact_mod_cast hn
  have hmR : (1:ℝ) ≤ m:=by exact_mod_cast hm
  have hmnR : (m:ℝ)≤n:=by exact_mod_cast hmn
  let γ:=vertexProfile n m a b
  let i : Fin n:=⟨0,hn0⟩
  have hi : γ i=b:=by dsimp [γ,i,vertexProfile];rw [if_pos (by omega)]
  let G : ℝ := ∑ k,γ k
  let K : ℝ := G+((n:ℝ)-1)*b
  have hγ : ∀ i,0<γ i:=fun i=>ha.trans_le (vertex_weight_bounds n m a b hab i).1
  have hG : 0<G:=weight_sum_pos hn0 γ hγ
  have hK : 0<K:=by dsimp [K];nlinarith
  have hnorm : K⁻¹*((∑ k,γ k)+((n:ℝ)-1)*γ i)=1 := by rw [hi];exact inv_mul_cancel₀ hK.ne'
  have hp:=fan_primal γ i K⁻¹ (inv_nonneg.mpr hK.le) hnorm
  have hle:=primal_le_value γ _ _ _ (fun i=>(hγ i).le) hp.1
  rw [hp.2,hi] at hle
  have hGs : G=(m:ℝ)*b+((n:ℝ)-m)*a:=vertex_sum n m hmn a b
  have hKQ : K=b*((n:ℝ)+m+(1-heterogeneity a b)*((n:ℝ)-m)-1) := by
    dsimp [K]
    rw [hGs]
    unfold heterogeneity
    field_simp
    <;> ring
  have heq : ((n:ℝ)-1)*b*K⁻¹=((n:ℝ)-1)/((n:ℝ)+m+(1-heterogeneity a b)*((n:ℝ)-m)-1) := by
    rw [hKQ]
    field_simp
  rw [heq] at hle
  exact hle

theorem vertex_primal_heterogeneity (n m : ℕ) (hm : 1 ≤ m) (hmn : m<n)
    (a b : ℝ) (ha : 0<a) (hab : a≤b) : heterogeneity a b≤lpValue (vertexProfile n m a b) := by
  have hn0 : 0<n:=by omega
  let γ:=vertexProfile n m a b
  let i : Fin n:=⟨0,hn0⟩
  let j : Fin n:=⟨m,hmn⟩
  have hi : γ i=b:=by dsimp [γ,i,vertexProfile];rw [if_pos (by omega)]
  have hj : γ j=a:=by simp [γ,j,vertexProfile]
  have hb : 0<b:=ha.trans_le hab
  have hp:=single_edge_primal γ i j (by rw [hi];exact hb)
  have hle:=primal_le_value γ _ _ _ (fun k=>(ha.trans_le (vertex_weight_bounds n m a b hab k).1).le) hp.1
  rw [hp.2,hi,hj] at hle
  exact hle

theorem vertex_value_exact (n m : ℕ) (a b : ℝ) (ha : 0<a) (hab : a≤b)
    (hm : 1 ≤ m) (hmn : m≤n)
    (hcorr : m<n ∨ heterogeneity a b≤((n:ℝ)-1)/(2*(n:ℝ)-1)) :
    lpValue (vertexProfile n m a b)=lemma2Value n m (heterogeneity a b) := by
  have hn0 : 0<n:=by omega
  have hγ : ∀ i,0<vertexProfile n m a b i:=fun i=>ha.trans_le (vertex_weight_bounds n m a b hab i).1
  by_cases hn : n=1
  · subst n
    have hm1 : m=1:=by omega
    subst m
    rw [singleton_lp _ hγ]
    have hd:=heterogeneity_range a b ha hab
    have hc : heterogeneity a b=0:=by rcases hcorr with h|h;omega;norm_num at h;linarith
    simp [lemma2Value,hc]
  · have hn2 : 1<n:=by omega
    obtain ⟨lam,hl⟩:=vertex_dual_opt_bound n m hn2 hm hmn a b ha hab
    apply le_antisymm (lp_le_dual_certificate hn0 _ hγ _ lam hl)
    have hf:=vertex_primal_floor n m hn2 hm hmn a b ha hab
    unfold lemma2Value
    apply max_le _ hf
    rcases hcorr with h|h
    · exact vertex_primal_heterogeneity n m hm h a b ha hab
    · by_cases hmn' : m<n
      · exact vertex_primal_heterogeneity n m hm hmn' a b ha hab
      · have he : m=n:=by omega
        subst m
        have heq : (n:ℝ)+n+(1-heterogeneity a b)*((n:ℝ)-n)-1=2*(n:ℝ)-1:=by ring
        rw [heq] at hf
        exact h.trans hf
end Queelius.ProviderGuarantee

end

section
namespace ProviderGuarantee.Bound

theorem lemma_1 {D : Type*} [Fintype D] [DecidableEq D] {n : ℕ} (v : D → ℝ)
    (γmin γmax : ℝ) (hγmin : 0 < γmin) (hγ : γmin ≤ γmax)
    (γ : Fin n → ℝ) (hγmem : ∀ i, γ i ∈ Set.Icc γmin γmax)
    (F FG : Set (Fin n → Finset D)) (h1 : Assumption1 F) (h2 : Assumption2 v F FG)
    (A B : Fin n → Finset D) (hA : IsOptimal γ v F A) (hB : IsOptimal γ v FG B) :
    ∀ i j, val v (A i \ Finset.univ.biUnion B) ≤ val v (B j \ A i) := by
  exact Queelius.ProviderGuarantee.exchange_from_feasible v γ (fun i=>lt_of_lt_of_le hγmin (hγmem i).1) F FG h1 h2 A B hA.1 hB

end ProviderGuarantee.Bound

namespace ProviderGuarantee.Bound

theorem reduction_eq_11_12 {D : Type*} [Fintype D] [DecidableEq D] {n : ℕ} (v : D → ℝ)
    (γmin γmax : ℝ) (hγmin : 0 < γmin) (hγ : γmin ≤ γmax)
    (γ : Fin n → ℝ) (hγmem : ∀ i, γ i ∈ Set.Icc γmin γmax)
    (F FG : Set (Fin n → Finset D)) (h1 : Assumption1 F) (h2 : Assumption2 v F FG)
    (A B : Fin n → Finset D) (hA : IsOptimal γ v F A) (hB : IsOptimal γ v FG B) :
    let x : Fin n → ℝ := fun i => val v (A i \ Finset.univ.biUnion B)
    let y : Fin n → ℝ := fun i => val v (B i \ Finset.univ.biUnion A)
    let w : Fin n → Fin n → ℝ := fun i j => val v (A i ∩ B j)
    (∀ i j, x i ≤ ∑ k, w k j - w i j + y j) ∧
    (∀ i, val v (A i) = x i + ∑ j, w i j) ∧
    (∀ j, val v (B j) = y j + ∑ i, w i j) ∧
    (∀ i, 0 ≤ x i) ∧ (∀ i, 0 ≤ y i) ∧ (∀ i j, 0 ≤ w i j) ∧
    valueLoss γ v F FG =
      (∑ i, γ i * x i - ∑ i, γ i * y i + ∑ i, ∑ j, w i j * (γ i - γ j)) /
        (∑ i, γ i * x i + ∑ i, ∑ j, w i j * γ i) := by
  exact Queelius.ProviderGuarantee.allocation_scalar_reduction v γ (fun i=>lt_of_lt_of_le hγmin (hγmem i).1) F FG h1 h2 A B hA hB

end ProviderGuarantee.Bound

namespace ProviderGuarantee.Bound

theorem lp_bound {D : Type*} [Fintype D] [DecidableEq D] {n : ℕ} (v : D → ℝ)
    (γmin γmax : ℝ) (hγmin : 0 < γmin) (hγ : γmin ≤ γmax)
    (γ : Fin n → ℝ) (hγmem : ∀ i, γ i ∈ Set.Icc γmin γmax)
    (F FG : Set (Fin n → Finset D)) (h1 : Assumption1 F) (h2 : Assumption2 v F FG)
    (hFG : FG.Nonempty) :
    valueLoss γ v F FG ≤ lpValue γ := by
  exact Queelius.ProviderGuarantee.allocation_loss_le_lp v γ (fun i=>lt_of_lt_of_le hγmin (hγmem i).1) F FG h1 h2 hFG

end ProviderGuarantee.Bound

namespace ProviderGuarantee.Bound

theorem dualValue_quasiconvexOn {n : ℕ} (γmin γmax : ℝ) (hγmin : 0 < γmin) (hγ : γmin ≤ γmax) :
    QuasiconvexOn ℝ (Set.Icc (fun _ : Fin n => γmin) (fun _ => γmax)) dualValue ∧
    ∀ γ ∈ Set.Icc (fun _ : Fin n => γmin) (fun _ => γmax),
      0 ≤ dualValue γ ∧ dualValue γ ≤ 1 := by
  exact Queelius.ProviderGuarantee.dual_box_all γmin γmax hγmin

end ProviderGuarantee.Bound

namespace ProviderGuarantee.Bound

theorem lemma2Value_antitone (n : ℕ) (γmin γmax : ℝ) (hγmin : 0 < γmin) (hγ : γmin ≤ γmax)
    (n0 n0' : ℕ) (h1 : 1 ≤ n0) (h2 : n0 ≤ n0') (h3 : n0' ≤ n) :
    lemma2Value n n0' (heterogeneity γmin γmax) ≤ lemma2Value n n0 (heterogeneity γmin γmax) ∧
    lemma2Value n 1 (heterogeneity γmin γmax) = lossBound n (heterogeneity γmin γmax) := by
  exact Queelius.ProviderGuarantee.vertex_order_all n γmin γmax hγmin hγ n0 n0' h1 h2 h3

end ProviderGuarantee.Bound

end

section
noncomputable section
open Finset
namespace Queelius.ProviderGuarantee
open ProviderGuarantee.Bound

theorem dual_permute {n : ℕ} (σ : Equiv.Perm (Fin n)) (γ : Fin n→ℝ)
    (s : ℝ) (lam : Fin n→Fin n→ℝ) (h : DualFeasible γ s lam) :
    DualFeasible (fun i=>γ (σ i)) s (fun i j=>lam (σ i) (σ j)) := by
  have hs (f : Fin n→ℝ) : (∑ i,f (σ i))=∑ i,f i:=Equiv.sum_comp σ f
  have he (f : Fin n→ℝ) (k : Fin n) :
      (∑ i∈univ.erase k,f (σ i))=∑ i∈univ.erase (σ k),f i := by
    have h1:=sum_erase_add univ (fun i=>f (σ i)) (mem_univ k)
    have h2:=sum_erase_add univ f (mem_univ (σ k))
    rw [hs] at h1
    linarith
  refine ⟨?_,?_,?_,?_⟩
  · intro i
    simpa only [hs] using h.1 (σ i)
  · intro k j
    change 0≤γ (σ j)-γ (σ k)+s*γ (σ k)-(∑ i∈univ.erase k,lam (σ i) (σ j))
    rw [he (fun i=>lam i (σ j)) k]
    exact h.2.1 (σ k) (σ j)
  · intro j
    change (∑ i,lam (σ i) (σ j))≤γ (σ j)
    rw [hs (fun i=>lam i (σ j))]
    exact h.2.2.1 (σ j)
  · intro i j;exact h.2.2.2 (σ i) (σ j)

theorem prefix_card (n m : ℕ) (hm : m≤n) :
    (univ.filter (fun i : Fin n=>(i:ℕ) < m)).card=m := by
  classical
  rcases eq_or_lt_of_le hm with h|h
  · subst m;simp
  · have heq : univ.filter (fun i : Fin n=>(i:ℕ) < m)=Iio (⟨m,h⟩:Fin n) := by
      ext i;simp [Fin.lt_def]
    rw [heq,Fin.card_Iio]

theorem endpoint_profile_permutation {n : ℕ} (a b : ℝ) (γ : Fin n→ℝ)
    (hγ : ∀ i,γ i=a ∨ γ i=b) :
    ∃ m≤n,∃ σ : Equiv.Perm (Fin n),γ=fun i=>vertexProfile n m a b (σ i) := by
  classical
  let H:=univ.filter (fun i=>γ i=b)
  let m:=H.card
  have hm : m≤n:=by simpa [m] using card_le_card (filter_subset (fun i=>γ i=b) univ)
  let P:=univ.filter (fun i : Fin n=>(i:ℕ) < m)
  have hc : H.card=P.card:=by dsimp [P];rw [prefix_card n m hm]
  obtain ⟨σ,hσ⟩:=Equiv.Perm.exists_map_finset_eq H P hc
  refine ⟨m,hm,σ,?_⟩
  have he (i : Fin n) : γ i=b ↔ (σ i:ℕ) < m := by
    have hh : σ i∈P ↔ i∈H:=by rw [←hσ];simp
    simpa [H,P] using hh.symm
  funext i
  dsimp [vertexProfile]
  by_cases hi : γ i=b
  · simp [hi, (he i).mp hi]
  · simp only [if_neg (fun h=>hi ((he i).mpr h))]
    exact (hγ i).resolve_right hi
end Queelius.ProviderGuarantee

end

section
noncomputable section
open Finset
namespace Queelius.ProviderGuarantee
open ProviderGuarantee.Bound

theorem homogeneous_lp_value (n : ℕ) (hn : 0<n) (b : ℝ) (hb : 0<b) :
    lpValue (fun _ : Fin n=>b)=((n:ℝ)-1)/(2*(n:ℝ)-1) := by
  have hnR : (1:ℝ)≤n:=by exact_mod_cast hn
  have hz : heterogeneity b b=0:=by simp [heterogeneity]
  have hbound : 0≤((n:ℝ)-1)/(2*(n:ℝ)-1):=div_nonneg (by linarith) (by linarith)
  have h:=vertex_value_exact n n b b hb le_rfl (by omega) le_rfl (Or.inr (by rw [hz];exact hbound))
  have hp : vertexProfile n n b b=(fun _ : Fin n=>b):=by funext i;simp [vertexProfile]
  rw [hp,hz] at h
  simpa [lemma2Value,show (n:ℝ)+(n:ℝ)-1=2*(n:ℝ)-1 by ring,max_eq_right hbound] using h

theorem all_high_actual_value (n : ℕ) (hn : 0<n) (a b : ℝ) (hb : 0<b) :
    lpValue (vertexProfile n n a b)=((n:ℝ)-1)/(2*(n:ℝ)-1) := by
  have hp : vertexProfile n n a b=(fun _ : Fin n=>b):=by funext i;simp [vertexProfile]
  rw [hp]
  exact homogeneous_lp_value n hn b hb

namespace Controls
-- This reproduces the platform's existing correction; it is not a new discovery.
theorem all_high_excluded_case :
    lpValue (vertexProfile 2 2 (1/2) 1)=1/3 ∧
    lemma2Value 2 2 (heterogeneity (1/2) 1)=1/2 := by
  constructor
  · have h:=all_high_actual_value 2 (by norm_num) (1/2) 1 (by norm_num)
    norm_num at h ⊢
    exact h
  · norm_num [lemma2Value,heterogeneity]

theorem heterogeneous_delta_regime : lpValue (vertexProfile 2 1 (1/4) 1)=3/4 := by
  have h:=vertex_value_exact 2 1 (1/4) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (Or.inl (by norm_num))
  norm_num [lemma2Value,heterogeneity] at h
  exact h

theorem heterogeneous_fraction_regime : lpValue (vertexProfile 2 1 (3/4) 1)=4/11 := by
  have h:=vertex_value_exact 2 1 (3/4) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (Or.inl (by norm_num))
  norm_num [lemma2Value,heterogeneity] at h
  exact h

-- Equality between the two regimes is covered without a strict-inequality gap.
theorem regime_boundary : lpValue (vertexProfile 2 1 ((Real.sqrt 5-1)/2) 1)=(3-Real.sqrt 5)/2 := by
  have hs0 : 0≤Real.sqrt 5:=Real.sqrt_nonneg _
  have hs2 : (Real.sqrt 5)^2=5:=Real.sq_sqrt (by norm_num)
  have hs1 : 1<Real.sqrt 5:=by nlinarith
  have hs3 : Real.sqrt 5<3:=by nlinarith
  have h:=vertex_value_exact 2 1 ((Real.sqrt 5-1)/2) 1 (by linarith) (by linarith) (by norm_num) (by norm_num) (Or.inl (by norm_num))
  have he : heterogeneity ((Real.sqrt 5-1)/2) 1=(3-Real.sqrt 5)/2:=by unfold heterogeneity;ring
  rw [he] at h
  have hr : (1:ℝ)/(2+(1-(3-Real.sqrt 5)/2))=(3-Real.sqrt 5)/2 := by
    apply (div_eq_iff (show 2+(1-(3-Real.sqrt 5)/2)≠0 by linarith)).mpr
    nlinarith
  norm_num only [lemma2Value,Nat.cast_ofNat,Nat.cast_one] at h
  convert h using 1
  have hd : (3:ℝ)+(1-(3-Real.sqrt 5)/2)*1-1=2+(1-(3-Real.sqrt 5)/2):=by ring
  rw [hd]
  norm_num only [show (2:ℝ)-1=1 by norm_num]
  rw [hr,max_self]
end Controls
end Queelius.ProviderGuarantee

end

section
theorem ProviderGuarantee.Bound.lemma_2 : (
∀ (n n0 : Nat) (γmin γmax : Real),
  @LT.lt Real Real.instLT (@OfNat.ofNat Real (nat_lit 0) (@Zero.toOfNat0 Real Real.instZero)) γmin →
    @LE.le Real Real.instLE γmin γmax →
      @LE.le Nat instLENat (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) n0 →
        @LE.le Nat instLENat n0 n →
          Or (@LT.lt Nat instLTNat n0 n)
              (@LE.le Real Real.instLE (ProviderGuarantee.Bound.heterogeneity γmin γmax)
                (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))
                  (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@Nat.cast Real Real.instNatCast n)
                    (@OfNat.ofNat Real (nat_lit 1) (@One.toOfNat1 Real Real.instOne)))
                  (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
                    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
                      (@OfNat.ofNat Real (nat_lit 2)
                        (@instOfNatAtLeastTwo Real (nat_lit 2) Real.instNatCast
                          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                            (@Nat.instNeZeroSucc (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                      (@Nat.cast Real Real.instNatCast n))
                    (@OfNat.ofNat Real (nat_lit 1) (@One.toOfNat1 Real Real.instOne))))) →
            @Eq Real (@ProviderGuarantee.Bound.lpValue n (ProviderGuarantee.Bound.vertexProfile n n0 γmin γmax))
              (ProviderGuarantee.Bound.lemma2Value n n0 (ProviderGuarantee.Bound.heterogeneity γmin γmax))
) := @Queelius.ProviderGuarantee.vertex_value_exact

end

section
noncomputable section
open Finset
namespace Queelius.ProviderGuarantee
open ProviderGuarantee.Bound

theorem loss_bound_monotone (n : ℕ) (hn : 1 ≤ n) (δ ε : ℝ)
    (hd : δ ≤ ε) (he : ε < 1) : lossBound n δ ≤ lossBound n ε := by
  have hnR : (1:ℝ) ≤ n:=by exact_mod_cast hn
  have hden : 0 < (n:ℝ)+(1-ε)*((n:ℝ)-1) := by
    have :=mul_nonneg (show 0 ≤ 1-ε by linarith) (show 0 ≤ (n:ℝ)-1 by linarith)
    linarith
  have hdenle : (n:ℝ)+(1-ε)*((n:ℝ)-1) ≤ (n:ℝ)+(1-δ)*((n:ℝ)-1) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hd) (show 0 ≤ (n:ℝ)-1 by linarith)]
  exact max_le_max hd (div_le_div_of_nonneg_left (by linarith) hden hdenle)

theorem endpoint_dual_bound (n : ℕ) (hn : 1 < n) (a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (γ : Fin n→ℝ) (hγ : ∀ i,γ i=a ∨ γ i=b) :
    dualValue γ ≤ lossBound n (heterogeneity a b) := by
  have hpos : ∀ i,0 < γ i := by
    intro i;rcases hγ i with h|h
    · rw [h];exact ha
    · rw [h];exact ha.trans_le hab
  have hr:=heterogeneity_range a b ha hab
  obtain ⟨m,hmn,σ,hprofile⟩:=endpoint_profile_permutation a b γ hγ
  by_cases hm : 1 ≤ m
  · obtain ⟨lam,hl⟩:=vertex_dual_opt_bound n m hn hm hmn a b ha hab
    have ht:=dual_permute σ _ _ _ hl
    rw [←hprofile] at ht
    have hbnd:=dual_value_le_certificate (by omega) γ hpos _ _ ht
    have ho:=vertex_value_antitone n 1 m le_rfl hm hmn _ hr.1 hr.2
    rw [first_vertex_bound] at ho
    exact hbnd.trans ho
  · have hm0 : m=0:=by omega
    have hc : γ=(fun _=>a) := by
      rw [hprofile,hm0];funext i;simp [vertexProfile]
    obtain ⟨lam,hl⟩:=vertex_dual_opt_bound n n hn (by omega) le_rfl a a ha le_rfl
    have hz : heterogeneity a a=0:=by simp [heterogeneity]
    have hp : vertexProfile n n a a=(fun _=>a):=by funext i;simp [vertexProfile]
    rw [hp,←hc,hz] at hl
    have hbnd:=dual_value_le_certificate (by omega) γ hpos _ _ hl
    have ho:=vertex_value_antitone n 1 n le_rfl (by omega) le_rfl 0 (by norm_num) (by norm_num)
    rw [first_vertex_bound] at ho
    exact hbnd.trans (ho.trans (loss_bound_monotone n (by omega) 0 _ hr.1 hr.2))

theorem arbitrary_profile_lp_bound (n : ℕ) (a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (γ : Fin n→ℝ) (hγ : ∀ i,γ i∈Set.Icc a b) :
    lpValue γ ≤ lossBound n (heterogeneity a b) := by
  have hp : ∀ i,0 < γ i:=fun i=>ha.trans_le (hγ i).1
  have hr:=heterogeneity_range a b ha hab
  have hnonneg : 0 ≤ lossBound n (heterogeneity a b):=hr.1.trans (le_max_left _ _)
  rcases Nat.eq_zero_or_pos n with hn0|hn
  · subst n
    simpa [lpValue,PrimalFeasible] using hnonneg
  · by_cases hn1 : n=1
    · subst n
      rw [singleton_lp γ hp]
      exact hnonneg
    · have hn2 : 1 < n:=by omega
      have hmem : γ∈Set.Icc (fun _=>a) (fun _=>b):=⟨fun i=>(hγ i).1,fun i=>(hγ i).2⟩
      obtain ⟨η,hη,hvert,hdom⟩:=box_vertex (fun _=>a) (fun _=>b) dualValue
        (dual_box_quasiconvex a b ha) γ hmem
      exact (dual_value_bounds hn γ hp).2.2 |>.trans (hdom.trans (endpoint_dual_bound n hn2 a b ha hab η hvert))

theorem provider_guarantee_root {D : Type*} [Fintype D] [DecidableEq D]
    (n : ℕ) (v : D→ℝ) (a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (γ : Fin n→ℝ) (hγ : ∀ i,γ i∈Set.Icc a b)
    (F FG : Set (Fin n→Finset D)) (h1 : Assumption1 F) (h2 : Assumption2 v F FG)
    (hFG : FG.Nonempty) : valueLoss γ v F FG ≤ lossBound n (heterogeneity a b) := by
  exact (allocation_loss_le_lp v γ (fun i=>ha.trans_le (hγ i).1) F FG h1 h2 hFG).trans
    (arbitrary_profile_lp_bound n a b ha hab γ hγ)
end Queelius.ProviderGuarantee

end

section
noncomputable section
namespace Queelius.ProviderGuarantee
open ProviderGuarantee.Bound

theorem dual_value_permute {n : ℕ} (σ : Equiv.Perm (Fin n)) (γ : Fin n→ℝ) :
    dualValue (fun i=>γ (σ i))=dualValue γ := by
  have he : {s | ∃ lam,DualFeasible (fun i=>γ (σ i)) s lam}=
      {s | ∃ lam,DualFeasible γ s lam} := by
    ext s
    constructor
    · rintro ⟨lam,hl⟩
      have h:=dual_permute σ.symm _ _ _ hl
      exact ⟨_,by simpa using h⟩
    · rintro ⟨lam,hl⟩
      exact ⟨_,dual_permute σ _ _ _ hl⟩
  exact congrArg sInf he

namespace Controls
-- Includes an interior coordinate and places the maximum before the minimum.
theorem interior_unsorted_profile_bound :
    lpValue (![3,1,2] : Fin 3→ℝ) ≤ (2/3:ℝ) := by
  have h:=arbitrary_profile_lp_bound 3 1 3 (by norm_num) (by norm_num)
    (![3,1,2] : Fin 3→ℝ) (by intro i;fin_cases i <;> norm_num)
  norm_num [lossBound,heterogeneity] at h
  exact h

-- At zero heterogeneity the positive loss bound is attained by the LP;
-- this does not assert an allocation-system attainment theorem.
theorem homogeneous_root_sharp_at_lp :
    lpValue (fun _ : Fin 2=>(1:ℝ))=lossBound 2 (heterogeneity 1 1) ∧
    lossBound 2 (heterogeneity 1 1)=1/3 := by
  have h:=homogeneous_lp_value 2 (by norm_num) 1 (by norm_num)
  norm_num [lossBound,heterogeneity] at h ⊢
  exact h
end Controls
end Queelius.ProviderGuarantee

end

section
universe audit_u0
theorem submission_primary_solution : (
∀ {D : Type audit_u0} [Fintype D] [DecidableEq D] (n : Nat) (v : D → Real) (γmin γmax : Real),
  @LT.lt Real Real.instLT (@OfNat.ofNat Real (nat_lit 0) (@Zero.toOfNat0 Real Real.instZero)) γmin →
    @LE.le Real Real.instLE γmin γmax →
      ∀ (γ : Fin n → Real),
        (∀ (i : Fin n),
            @Membership.mem Real (Set Real) (@Set.instMembership Real) (@Set.Icc Real Real.instPreorder γmin γmax)
              (γ i)) →
          ∀ (F FG : Set (Fin n → Finset D)),
            @ProviderGuarantee.Bound.Assumption1 D n F →
              @ProviderGuarantee.Bound.Assumption2 D n v F FG →
                @Set.Nonempty (Fin n → Finset D) FG →
                  @LE.le Real Real.instLE (@ProviderGuarantee.Bound.valueLoss D n γ v F FG)
                    (ProviderGuarantee.Bound.lossBound n (ProviderGuarantee.Bound.heterogeneity γmin γmax))
) := @Queelius.ProviderGuarantee.provider_guarantee_root

end

section
noncomputable section
open Finset Matrix
namespace Queelius.ProviderGuarantee.Controls
open ProviderGuarantee.Bound

def asymmetricWeights : Fin 2 → ℝ := ![2,1]
def asymmetricFlow : Fin 2 → Fin 2 → ℝ := fun i j => if i=0 ∧ j=1 then 1/2 else 0
def standardMultiplier : LPRow 2 → ℝ
  | none => -1/2
  | some ij => if ij=(1,1) then 0 else -1/2

theorem asymmetric_primal : PrimalFeasible asymmetricWeights 0 0 asymmetricFlow := by
  refine ⟨?_,?_,by simp,by simp,?_⟩
  · norm_num [asymmetricWeights,asymmetricFlow,Fin.sum_univ_two]
  · intro i j
    fin_cases i <;> fin_cases j <;> norm_num [asymmetricFlow,Fin.sum_univ_two]
  · intro i j
    unfold asymmetricFlow
    split_ifs <;> norm_num

theorem asymmetric_standard_dual :
    ∀ c, (∑ r, stdMatrix asymmetricWeights r c * standardMultiplier r) ≤ stdCost asymmetricWeights c := by
  intro c
  rcases c with i | c
  · rw [std_dual_x]
    fin_cases i <;> norm_num [stdCost,asymmetricWeights,standardMultiplier,Fin.sum_univ_two]
  rcases c with i | c
  · rw [std_dual_y]
    fin_cases i <;> norm_num [stdCost,asymmetricWeights,standardMultiplier,Fin.sum_univ_two]
  rcases c with ⟨i,j⟩ | ⟨i,j⟩
  · rw [std_dual_w]
    fin_cases i <;> fin_cases j <;>
      norm_num [stdCost,asymmetricWeights,standardMultiplier,Fin.sum_univ_two]
  · rw [std_dual_z]
    fin_cases i <;> fin_cases j <;>
      norm_num [stdCost,standardMultiplier]

theorem asymmetric_decoded_dual :
    DualFeasible asymmetricWeights (1/2) (fun i j => -standardMultiplier (some (i,j))) := by
  have h := decode_std_dual asymmetricWeights standardMultiplier asymmetric_standard_dual
  norm_num [standardMultiplier] at h ⊢
  exact h

theorem asymmetric_optimal_values : lpValue asymmetricWeights = 1/2 ∧ dualValue asymmetricWeights = 1/2 := by
  have hγ (i) : 0 < asymmetricWeights i := by fin_cases i <;> norm_num [asymmetricWeights]
  have hlo := primal_le_value asymmetricWeights 0 0 asymmetricFlow (fun i => (hγ i).le) asymmetric_primal
  have hhi := lp_le_dual_certificate (by norm_num : 0<2) asymmetricWeights hγ _ _ asymmetric_decoded_dual
  have hp : lpValue asymmetricWeights = 1/2 := by
    norm_num [primalObj,asymmetricWeights,asymmetricFlow,Fin.sum_univ_two] at hlo
    exact le_antisymm hhi hlo
  exact ⟨hp,(duality_equality (by norm_num) asymmetricWeights hγ).symm.trans hp⟩

theorem positive_residual_slack :
    encodePrimal (0 : Fin 2 → ℝ) 0 asymmetricFlow
      (fun i j => (∑ k, asymmetricFlow k j) - asymmetricFlow i j)
      (.inr (.inr (.inr (1,1)))) = 1/2 := by
  norm_num [encodePrimal,asymmetricFlow,Fin.sum_univ_two]

theorem asymmetric_standard_objective :
    (∑ c, stdCost asymmetricWeights c *
      encodePrimal (0 : Fin 2 → ℝ) 0 asymmetricFlow
        (fun i j => (∑ k, asymmetricFlow k j) - asymmetricFlow i j) c) = -1/2 ∧
    (∑ r, stdRhs r * standardMultiplier r) = -1/2 := by
  constructor
  · rw [std_objective]
    norm_num [encodePrimal,primalObj,asymmetricWeights,asymmetricFlow,Fin.sum_univ_two]
  · rw [std_dual_objective]
    norm_num [standardMultiplier]

end Queelius.ProviderGuarantee.Controls

end

universe audit_u0

theorem solution : (
  ∀ {D : Type audit_u0} [Fintype D] [inst : DecidableEq D] {n : Nat} (v : D → Real) (γmin γmax : Real),
    @LT.lt Real Real.instLT (@OfNat.ofNat Real (nat_lit 0) (@Zero.toOfNat0 Real Real.instZero)) γmin →
      @LE.le Real Real.instLE γmin γmax →
        ∀ (γ : Fin n → Real),
          (∀ (i : Fin n),
              @Membership.mem Real (Set Real) (@Set.instMembership Real) (@Set.Icc Real Real.instPreorder γmin γmax)
                (γ i)) →
            ∀ (F FG : Set (Fin n → Finset D)),
              @ProviderGuarantee.Bound.Assumption1 D n F →
                @ProviderGuarantee.Bound.Assumption2 D n v F FG →
                  ∀ (A B : Fin n → Finset D),
                    @ProviderGuarantee.Bound.IsOptimal D n γ v F A →
                      @ProviderGuarantee.Bound.IsOptimal D n γ v FG B →
                        have x := fun (i : Fin n) =>
                          @ProviderGuarantee.Bound.val D v
                            (@SDiff.sdiff (Finset D) (@Finset.instSDiff D inst) (A i)
                              (@Finset.biUnion (Fin n) D inst (@Finset.univ (Fin n) (Fin.fintype n)) B));
                        have y := fun (i : Fin n) =>
                          @ProviderGuarantee.Bound.val D v
                            (@SDiff.sdiff (Finset D) (@Finset.instSDiff D inst) (B i)
                              (@Finset.biUnion (Fin n) D inst (@Finset.univ (Fin n) (Fin.fintype n)) A));
                        have w := fun (i j : Fin n) =>
                          @ProviderGuarantee.Bound.val D v
                            (@Inter.inter (Finset D) (@Finset.instInter D inst) (A i) (B j));
                        And
                          (∀ (i j : Fin n),
                            @LE.le Real Real.instLE (x i)
                              (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd)
                                (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
                                  (@Finset.sum (Fin n) Real Real.instAddCommMonoid (@Finset.univ (Fin n) (Fin.fintype n))
                                    fun (k : Fin n) => w k j)
                                  (w i j))
                                (y j)))
                          (And
                            (∀ (i : Fin n),
                              @Eq Real (@ProviderGuarantee.Bound.val D v (A i))
                                (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (x i)
                                  (@Finset.sum (Fin n) Real Real.instAddCommMonoid (@Finset.univ (Fin n) (Fin.fintype n))
                                    fun (j : Fin n) => w i j)))
                            (And
                              (∀ (j : Fin n),
                                @Eq Real (@ProviderGuarantee.Bound.val D v (B j))
                                  (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (y j)
                                    (@Finset.sum (Fin n) Real Real.instAddCommMonoid
                                      (@Finset.univ (Fin n) (Fin.fintype n)) fun (i : Fin n) => w i j)))
                              (And
                                (∀ (i : Fin n),
                                  @LE.le Real Real.instLE
                                    (@OfNat.ofNat Real (nat_lit 0) (@Zero.toOfNat0 Real Real.instZero)) (x i))
                                (And
                                  (∀ (i : Fin n),
                                    @LE.le Real Real.instLE
                                      (@OfNat.ofNat Real (nat_lit 0) (@Zero.toOfNat0 Real Real.instZero)) (y i))
                                  (And
                                    (∀ (i j : Fin n),
                                      @LE.le Real Real.instLE
                                        (@OfNat.ofNat Real (nat_lit 0) (@Zero.toOfNat0 Real Real.instZero)) (w i j))
                                    (@Eq Real (@ProviderGuarantee.Bound.valueLoss D n γ v F FG)
                                      (@HDiv.hDiv Real Real Real
                                        (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))
                                        (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd)
                                          (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
                                            (@Finset.sum (Fin n) Real Real.instAddCommMonoid
                                              (@Finset.univ (Fin n) (Fin.fintype n)) fun (i : Fin n) =>
                                              @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (γ i) (x i))
                                            (@Finset.sum (Fin n) Real Real.instAddCommMonoid
                                              (@Finset.univ (Fin n) (Fin.fintype n)) fun (i : Fin n) =>
                                              @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (γ i) (y i)))
                                          (@Finset.sum (Fin n) Real Real.instAddCommMonoid
                                            (@Finset.univ (Fin n) (Fin.fintype n)) fun (i : Fin n) =>
                                            @Finset.sum (Fin n) Real Real.instAddCommMonoid
                                              (@Finset.univ (Fin n) (Fin.fintype n)) fun (j : Fin n) =>
                                              @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (w i j)
                                                (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (γ i) (γ j))))
                                        (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd)
                                          (@Finset.sum (Fin n) Real Real.instAddCommMonoid
                                            (@Finset.univ (Fin n) (Fin.fintype n)) fun (i : Fin n) =>
                                            @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (γ i) (x i))
                                          (@Finset.sum (Fin n) Real Real.instAddCommMonoid
                                            (@Finset.univ (Fin n) (Fin.fintype n)) fun (i : Fin n) =>
                                            @Finset.sum (Fin n) Real Real.instAddCommMonoid
                                              (@Finset.univ (Fin n) (Fin.fintype n)) fun (j : Fin n) =>
                                              @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (w i j)
                                                (γ i))))))))))
) := @ProviderGuarantee.Bound.reduction_eq_11_12
