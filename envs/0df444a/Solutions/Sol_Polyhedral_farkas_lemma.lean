-- Prove2me | solution 1 for Polyhedral.farkas_lemma
-- status  : ACCEPTED   (prove)
-- author  : @Hartmann_Psi
-- created : 2026-09-27T23:11:46.628694+00:00
-- url     : https://prove2.me/submissions/3d27c01c-a42c-41a3-90f3-cd0fdb5088b7

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

variable {m n : ℕ}

/-- The cone is stable under nonnegative scaling. -/
lemma smul_mem_coneOf (A : Matrix (Fin m) (Fin n) ℝ) {z : Fin m → ℝ} (hz : z ∈ coneOf A)
    {t : ℝ} (ht : 0 ≤ t) : t • z ∈ coneOf A := by
  obtain ⟨y, hy, rfl⟩ := hz
  exact ⟨t • y, fun j => mul_nonneg ht (hy j), by rw [Matrix.mulVec_smul]⟩

lemma zero_mem_coneOf (A : Matrix (Fin m) (Fin n) ℝ) : (0 : Fin m → ℝ) ∈ coneOf A :=
  ⟨0, fun _ => le_rfl, by simp⟩

/-- Every column of `A` lies in the cone. -/
lemma col_mem_coneOf (A : Matrix (Fin m) (Fin n) ℝ) (j : Fin n) :
    (fun i => A i j) ∈ coneOf A := by
  refine ⟨Pi.single j 1, fun k => ?_, ?_⟩
  · by_cases h : k = j <;> simp [Pi.single_apply, h]
  · funext i
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]

/-- **Farkas' lemma**: exactly one of `∃ x ≥ 0, A x = b` and
`∃ p, Aᵀ p ≥ 0 ∧ pᵀ b < 0` holds. -/
theorem farkas_lemma (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) :
    Xor (∃ x : Fin n → ℝ, 0 ≤ x ∧ A.mulVec x = b)
      (∃ p : Fin m → ℝ, 0 ≤ Aᵀ.mulVec p ∧ dotProduct p b < 0) := by
  by_cases hP : ∃ x : Fin n → ℝ, 0 ≤ x ∧ A.mulVec x = b
  · left
    refine ⟨hP, ?_⟩
    rintro ⟨p, hp, hpb⟩
    obtain ⟨x, hx, hAx⟩ := hP
    have h1 : dotProduct p b = dotProduct (Aᵀ.mulVec p) x := by
      rw [← hAx, Matrix.dotProduct_mulVec, Matrix.mulVec_transpose]
    have h2 : 0 ≤ dotProduct (Aᵀ.mulVec p) x :=
      Finset.sum_nonneg fun j _ => mul_nonneg (hp j) (hx j)
    rw [h1] at hpb
    linarith
  · right
    refine ⟨?_, hP⟩
    have hbnot : b ∉ coneOf A := by
      rintro ⟨y, hy, hAy⟩
      exact hP ⟨y, fun j => hy j, hAy⟩
    obtain ⟨f, u, hfs, hfb⟩ :=
      geometric_hahn_banach_closed_point (convex_coneOf A) (isClosed_coneOf A) hbnot
    have hu : 0 < u := by
      have h := hfs 0 (zero_mem_coneOf A)
      simpa using h
    have hcone_le : ∀ z ∈ coneOf A, f z ≤ 0 := by
      intro z hz
      by_contra hpos
      push_neg at hpos
      have ht : (0:ℝ) ≤ (u + 1) / f z := by positivity
      have hmem := smul_mem_coneOf A hz ht
      have h := hfs _ hmem
      rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ (ne_of_gt hpos)] at h
      linarith
    set p : Fin m → ℝ := fun i => - f (Pi.single i 1) with hpdef
    have hrepr : ∀ z : Fin m → ℝ, f z = - dotProduct p z := by
      intro z
      have hz : z = ∑ i, z i • (Pi.single i (1:ℝ)) := by
        funext k
        simp [Finset.sum_apply, Pi.single_apply]
      calc f z = f (∑ i, z i • (Pi.single i (1:ℝ))) := by rw [← hz]
        _ = ∑ i, z i * f (Pi.single i (1:ℝ)) := by
            rw [map_sum]; exact Finset.sum_congr rfl (fun i _ => by rw [map_smul, smul_eq_mul])
        _ = - dotProduct p z := by
            rw [dotProduct, ← Finset.sum_neg_distrib]
            exact Finset.sum_congr rfl (fun i _ => by simp [hpdef, mul_comm])
    refine ⟨p, ?_, ?_⟩
    · intro j
      have hcol : f (fun i => A i j) ≤ 0 := hcone_le _ (col_mem_coneOf A j)
      rw [hrepr] at hcol
      have : 0 ≤ dotProduct p (fun i => A i j) := by linarith
      simpa [Matrix.mulVec, dotProduct, Matrix.transpose_apply, mul_comm] using this
    · have h := hfb
      rw [hrepr] at h
      linarith

end FGCone

/-- Top-level entry point: Farkas' lemma. -/
theorem solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) :
    Xor (∃ x : Fin n → ℝ, 0 ≤ x ∧ A.mulVec x = b)
      (∃ p : Fin m → ℝ, 0 ≤ Aᵀ.mulVec p ∧ p ⬝ᵥ b < 0) :=
  FGCone.farkas_lemma A b
