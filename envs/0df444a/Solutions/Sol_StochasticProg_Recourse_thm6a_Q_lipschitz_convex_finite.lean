-- Prove2me | solution 1 for StochasticProg.Recourse.thm6a_Q_lipschitz_convex_finite
-- status  : ACCEPTED   (prove)
-- author  : @Hartmann_Psi
-- created : 2026-09-28T00:19:33.681719+00:00
-- url     : https://prove2.me/submissions/4e2b03dd-6428-431f-8b0f-63679c376511

import Mathlib
import Definitions.Def_StochasticProg_Recourse_Instance


open scoped BigOperators

namespace ConeGen

variable {ν ι : Type*} [Fintype ν] [Fintype ι]

/-- Conic Carathéodory: any nonnegative combination of a finite family of vectors can be
rewritten as a nonnegative combination supported on a linearly independent subfamily. -/
lemma exists_linearIndepOn_repr (v : ι → (ν → ℝ)) :
    ∀ (N : ℕ) (y : ι → ℝ), (∀ j, 0 ≤ y j) →
      {j | y j ≠ 0}.toFinset.card ≤ N →
      ∃ y' : ι → ℝ, (∀ j, 0 ≤ y' j) ∧ (∑ j, y' j • v j) = ∑ j, y j • v j ∧
        LinearIndepOn ℝ v {j | y' j ≠ 0} := by
  classical
  intro N
  induction N with
  | zero =>
      intro y hy hcard
      refine ⟨y, hy, rfl, ?_⟩
      have h0 : {j | y j ≠ 0}.toFinset = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hcard)
      have : {j : ι | y j ≠ 0} = ∅ := by
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
        set S : Finset ι := {j | y j ≠ 0}.toFinset with hS
        have hSset : (S : Set ι) = {j | y j ≠ 0} := by
          simp [hS]
        have hdep : ¬ LinearIndepOn ℝ v (S : Set ι) := by rwa [hSset]
        obtain ⟨f, hf0, j1, hj1S, hj1⟩ := not_linearIndepOn_finset_iff.mp hdep
        -- make `f` supported exactly on `S`
        set g : ι → ℝ := fun j => if j ∈ S then f j else 0 with hg
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
            ∃ mu : ι → ℝ, (∑ j, mu j • v j = 0) ∧ (∀ j, mu j ≠ 0 → j ∈ S) ∧
              ∃ j0, 0 < mu j0 := by
          obtain ⟨j, hj⟩ := hgne
          rcases lt_or_gt_of_ne hj with hneg | hpos
          · refine ⟨fun k => -g k, ?_, ?_, j, by linarith⟩
            · simp only [neg_smul, Finset.sum_neg_distrib, hgsum, neg_zero]
            · intro k hk; exact hgsupp k (by simpa using fun h => hk (by simp [h]))
          · exact ⟨g, hgsum, hgsupp, j, hpos⟩
        -- the blocking ratio
        set P : Finset ι := Finset.univ.filter (fun j => 0 < mu j) with hP
        have hPne : P.Nonempty := ⟨j0, by simp [hP, hj0pos]⟩
        obtain ⟨jm, hjmP, hjmmin⟩ := P.exists_min_image (fun j => y j / mu j) hPne
        set t : ℝ := y jm / mu jm with ht
        have hmujm : 0 < mu jm := by simpa [hP] using hjmP
        have ht0 : 0 ≤ t := div_nonneg (hy jm) hmujm.le
        set y' : ι → ℝ := fun j => y j - t * mu j with hy'
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
lemma isClosed_image_of_linearIndepOn (v : ι → (ν → ℝ)) (S : Finset ι)
    (hS : LinearIndepOn ℝ v (S : Set ι)) :
    IsClosed ((fun w : {x // x ∈ S} → ℝ => ∑ j, w j • v (j : ι)) '' {w | ∀ j, 0 ≤ w j}) := by
  classical
  set L : ({x // x ∈ S} → ℝ) →ₗ[ℝ] (ν → ℝ) :=
    Fintype.linearCombination ℝ (fun j : {x // x ∈ S} => v (j : ι)) with hL
  have hker : LinearMap.ker L = ⊥ := by
    refine LinearMap.ker_eq_bot'.mpr ?_
    intro w hw
    have hw' : ∑ j : {x // x ∈ S}, w j • v (j : ι) = 0 := hw
    set f : ι → ℝ := fun i => if h : i ∈ S then w ⟨i, h⟩ else 0 with hf
    have hfS : ∑ i ∈ S, f i • v i = 0 := by
      rw [← Finset.sum_attach S (fun i => f i • v i)]
      rw [← hw']
      rw [Finset.univ_eq_attach]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      simp [hf, j.2]
    have := linearIndepOn_finset_iff.mp hS f hfS
    funext j
    have hj := this (j : ι) j.2
    simpa [hf, j.2] using hj
  have hcl : IsClosed {w : {x // x ∈ S} → ℝ | ∀ j, 0 ≤ w j} := by
    rw [Set.setOf_forall]
    exact isClosed_iInter fun j => isClosed_le continuous_const (continuous_apply j)
  have heq : (fun w : {x // x ∈ S} → ℝ => ∑ j, w j • v (j : ι)) = ⇑L := by
    funext w
    simp only [hL, Fintype.linearCombination_apply]
  rw [heq]
  exact (LinearMap.isClosedEmbedding_of_injective (f := L) hker).isClosedMap _ hcl

/-- **Weyl's theorem**: the conic hull of finitely many vectors is closed. -/
theorem isClosed_coneSpan (v : ι → (ν → ℝ)) :
    IsClosed {z : ν → ℝ | ∃ y : ι → ℝ, (∀ j, 0 ≤ y j) ∧ ∑ j, y j • v j = z} := by
  classical
  have key : {z : ν → ℝ | ∃ y : ι → ℝ, (∀ j, 0 ≤ y j) ∧ ∑ j, y j • v j = z}
      = ⋃ S : {S : Finset ι // LinearIndepOn ℝ v (S : Set ι)},
          (fun w : {x // x ∈ S.1} → ℝ => ∑ j, w j • v (j : ι)) '' {w | ∀ j, 0 ≤ w j} := by
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨y', hy', hsum, hindep⟩ :=
        exists_linearIndepOn_repr v {j | y j ≠ 0}.toFinset.card y hy le_rfl
      have hindep' : LinearIndepOn ℝ v (({j | y' j ≠ 0}.toFinset : Finset ι) : Set ι) := by
        simpa [Set.coe_toFinset] using hindep
      refine Set.mem_iUnion.mpr ⟨⟨{j | y' j ≠ 0}.toFinset, hindep'⟩, ?_⟩
      refine ⟨fun j => y' (j : ι), fun j => hy' _, ?_⟩
      show ∑ j : {x // x ∈ {j | y' j ≠ 0}.toFinset}, y' (j : ι) • v (j : ι)
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
      set y : ι → ℝ := fun j => if h : j ∈ S.1 then w ⟨j, h⟩ else 0 with hy
      refine ⟨y, ?_, ?_⟩
      · intro j
        by_cases h : j ∈ S.1
        · simpa [hy, h] using hw ⟨j, h⟩
        · simp [hy, h]
      · have e1 : ∑ j, y j • v j = ∑ j ∈ S.1, y j • v j :=
          (Finset.sum_subset (Finset.subset_univ S.1) (fun j _ hj => by simp [hy, hj])).symm
        rw [e1, ← Finset.sum_attach S.1 (fun i => y i • v i)]
        show ∑ j ∈ S.1.attach, y (j : ι) • v (j : ι)
          = ∑ j : {x // x ∈ S.1}, w j • v (j : ι)
        rw [Finset.univ_eq_attach]
        exact Finset.sum_congr rfl (fun j _ => by simp [hy, j.2])
  rw [key]
  exact isClosed_iUnion_of_finite (fun S => isClosed_image_of_linearIndepOn v S.1 S.2)


/-- The cone generated by a finite family of vectors. -/
def coneSpan (v : ι → (ν → ℝ)) : Set (ν → ℝ) :=
  {z | ∃ y : ι → ℝ, (∀ j, 0 ≤ y j) ∧ ∑ j, y j • v j = z}

lemma isClosed_coneSpan' (v : ι → (ν → ℝ)) : IsClosed (coneSpan v) := isClosed_coneSpan v

lemma convex_coneSpan (v : ι → (ν → ℝ)) : Convex ℝ (coneSpan v) := by
  rintro z1 ⟨y1, hy1, rfl⟩ z2 ⟨y2, hy2, rfl⟩ a b ha hb _
  refine ⟨a • y1 + b • y2, fun j => by
    have := mul_nonneg ha (hy1 j); have := mul_nonneg hb (hy2 j)
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; linarith, ?_⟩
  rw [Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, smul_smul]
  module

lemma zero_mem_coneSpan (v : ι → (ν → ℝ)) : (0 : ν → ℝ) ∈ coneSpan v :=
  ⟨0, fun _ => le_rfl, by simp⟩

lemma smul_mem_coneSpan (v : ι → (ν → ℝ)) {z : ν → ℝ} (hz : z ∈ coneSpan v)
    {t : ℝ} (ht : 0 ≤ t) : t • z ∈ coneSpan v := by
  obtain ⟨y, hy, rfl⟩ := hz
  refine ⟨t • y, fun j => mul_nonneg ht (hy j), ?_⟩
  rw [Finset.smul_sum]
  exact Finset.sum_congr rfl (fun j _ => by simp [smul_smul])

lemma gen_mem_coneSpan [DecidableEq ι] (v : ι → (ν → ℝ)) (j : ι) : v j ∈ coneSpan v := by
  refine ⟨Pi.single j 1, fun k => ?_, ?_⟩
  · by_cases h : k = j <;> simp [Pi.single_apply, h]
  · simp [Pi.single_apply, Finset.sum_ite_eq']

/-- Every continuous linear functional on `ν → ℝ` is minus a dot product. -/
lemma frepr [DecidableEq ν] (f : (ν → ℝ) →L[ℝ] ℝ) (z : ν → ℝ) :
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

/-- **Separation form of Farkas' lemma** for an arbitrary finite family. -/
theorem exists_separating_of_notMem_coneSpan [DecidableEq ι] [DecidableEq ν]
    (v : ι → (ν → ℝ)) {b : ν → ℝ} (hb : b ∉ coneSpan v) :
    ∃ w : ν → ℝ, (∀ j, 0 ≤ dotProduct w (v j)) ∧ dotProduct w b < 0 := by
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
    have h := hcone_le _ (gen_mem_coneSpan v j)
    rw [hrepr] at h
    linarith
  · have hrepr := frepr f b
    rw [hrepr] at hfb
    linarith

end ConeGen

namespace LPGen

open ConeGen Matrix

variable {ρ κ : Type*} [Fintype ρ] [Fintype κ] [DecidableEq ρ] [DecidableEq κ]

/-- **Gale's theorem of the alternative** for arbitrary finite index types. -/
theorem gale_alternative (B : Matrix ρ κ ℝ) (c : ρ → ℝ)
    (hno : ¬ ∃ pi : κ → ℝ, ∀ i, Matrix.mulVec B pi i ≤ c i) :
    ∃ w : ρ → ℝ, (∀ i, 0 ≤ w i) ∧ Matrix.mulVec Bᵀ w = 0 ∧ dotProduct w c < 0 := by
  classical
  set v : (κ ⊕ κ) ⊕ ρ → (ρ → ℝ) := fun t =>
    match t with
    | Sum.inl (Sum.inl j) => fun i => B i j
    | Sum.inl (Sum.inr j) => fun i => -(B i j)
    | Sum.inr i => Pi.single i 1 with hv
  have hnotmem : c ∉ coneSpan v := by
    rintro ⟨y, hy, hsum⟩
    refine hno ⟨fun j => y (Sum.inl (Sum.inl j)) - y (Sum.inl (Sum.inr j)), ?_⟩
    intro i
    have hc : c i = Matrix.mulVec B (fun j => y (Sum.inl (Sum.inl j)) -
        y (Sum.inl (Sum.inr j))) i + y (Sum.inr i) := by
      rw [← hsum]
      rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
      simp only [Finset.sum_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hv,
        Matrix.mulVec, dotProduct]
      have h3 : ∑ x, y (Sum.inr x) * (Pi.single x (1:ℝ) : ρ → ℝ) i = y (Sum.inr i) := by
        simp [Pi.single_apply, Finset.sum_ite_eq']
      rw [h3]
      congr 1
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun x _ => by ring)
    have := hy (Sum.inr i)
    linarith [hc]
  obtain ⟨w, hwnn, hwc⟩ := exists_separating_of_notMem_coneSpan v hnotmem
  refine ⟨w, ?_, ?_, hwc⟩
  · intro i
    have h := hwnn (Sum.inr i)
    simpa [hv, dotProduct, Pi.single_apply] using h
  · funext j
    have h1 := hwnn (Sum.inl (Sum.inl j))
    have h2 := hwnn (Sum.inl (Sum.inr j))
    simp only [hv, dotProduct] at h1 h2
    have h2' : ∑ i, w i * B i j ≤ 0 := by
      have he : ∑ i, w i * -(B i j) = -∑ i, w i * B i j := by
        rw [← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl (fun i _ => by ring)
      rw [he] at h2; linarith
    have hz : ∑ i, w i * B i j = 0 := le_antisymm h2' h1
    simpa [Matrix.mulVec, dotProduct, Matrix.transpose_apply, mul_comm] using hz

variable {μ ν : Type*} [Fintype μ] [Fintype ν] [DecidableEq μ] [DecidableEq ν]

/-- **Strong duality with complementary slackness** for a standard-form linear program
over arbitrary finite index types. -/
theorem lp_strong_duality (M : Matrix μ ν ℝ) (dv : ν → ℝ) (g : μ → ℝ)
    (u0 : ν → ℝ) (hu0 : ∀ j, 0 ≤ u0 j) (hMu0 : Matrix.mulVec M u0 = g)
    (hopt : ∀ u : ν → ℝ, (∀ j, 0 ≤ u j) → Matrix.mulVec M u = g →
      dotProduct dv u0 ≤ dotProduct dv u) :
    ∃ pi : μ → ℝ, (∀ j, Matrix.mulVec Mᵀ pi j ≤ dv j) ∧
      dotProduct g pi = dotProduct dv u0 ∧
      ∀ j, u0 j * (dv j - Matrix.mulVec Mᵀ pi j) = 0 := by
  classical
  set val : ℝ := dotProduct dv u0 with hvaldef
  set B : Matrix (Unit ⊕ ν) μ ℝ :=
    Matrix.of (Sum.elim (fun _ j => -g j) (fun i' j => M j i')) with hB
  set cc : Unit ⊕ ν → ℝ := Sum.elim (fun _ => -val) dv with hcc
  have hB0 : ∀ j, B (Sum.inl ()) j = -g j := by intro j; simp [hB]
  have hBS : ∀ (i' : ν) (j), B (Sum.inr i') j = M j i' := by intro i' j; simp [hB]
  have hBrow0 : ∀ pi : μ → ℝ, Matrix.mulVec B pi (Sum.inl ()) = - dotProduct g pi := by
    intro pi
    simp only [Matrix.mulVec, dotProduct, hB0]
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  have hBrowS : ∀ (pi : μ → ℝ) (i' : ν),
      Matrix.mulVec B pi (Sum.inr i') = Matrix.mulVec Mᵀ pi i' := by
    intro pi i'
    simp only [Matrix.mulVec, dotProduct, hBS, Matrix.transpose_apply]
  have hsol : ∃ pi : μ → ℝ, ∀ i, Matrix.mulVec B pi i ≤ cc i := by
    by_contra hno
    obtain ⟨w, hwnn, hwB, hwc⟩ := gale_alternative B cc hno
    set t : ℝ := w (Sum.inl ()) with htdef
    set u : ν → ℝ := fun i' => w (Sum.inr i') with hudef
    have ht : 0 ≤ t := hwnn _
    have hu : ∀ i', 0 ≤ u i' := fun i' => hwnn _
    have hkey : ∀ j, Matrix.mulVec M u j = t * g j := by
      intro j
      have h := congrArg (fun f => f j) hwB
      simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Pi.zero_apply] at h
      rw [Fintype.sum_sum_type] at h
      rw [Fintype.sum_unique] at h
      rw [hB0 j] at h
      have h2 : ∑ i' : ν, B (Sum.inr i') j * w (Sum.inr i') = ∑ i' : ν, M j i' * u i' :=
        Finset.sum_congr rfl (fun i' _ => by rw [hBS])
      rw [h2] at h
      simp only [Matrix.mulVec, dotProduct]
      linarith
    have hobj : dotProduct dv u - t * val < 0 := by
      have h := hwc
      simp only [dotProduct] at h
      rw [Fintype.sum_sum_type, Fintype.sum_unique] at h
      have h2 : ∑ i' : ν, w (Sum.inr i') * cc (Sum.inr i') = ∑ i' : ν, dv i' * u i' := by
        refine Finset.sum_congr rfl (fun i' _ => ?_)
        simp only [hcc, Sum.elim_inr, hudef]
        ring
      rw [h2] at h
      have h3 : cc (Sum.inl ()) = -val := by simp [hcc]
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
      have hneg : dotProduct dv u < 0 := by rw [← htz] at hobj; linarith
      linarith [hstep]
    · set ub : ν → ℝ := fun j => u j / t with hubdef
      have hubnn : ∀ j, 0 ≤ ub j := fun j => div_nonneg (hu j) htp.le
      have hubM : Matrix.mulVec M ub = g := by
        funext j
        have hd : Matrix.mulVec M ub j = (Matrix.mulVec M u j) / t := by
          simp only [Matrix.mulVec, dotProduct, hubdef]
          rw [Finset.sum_div]
          exact Finset.sum_congr rfl (fun i _ => by ring)
        rw [hd, hkey j]
        field_simp
      have hstep := hopt _ hubnn hubM
      have h5 : dotProduct dv ub = (dotProduct dv u) / t := by
        simp only [dotProduct, hubdef]
        rw [Finset.sum_div]
        exact Finset.sum_congr rfl (fun i _ => by ring)
      rw [h5, le_div_iff₀ htp] at hstep
      have hcomm : val * t = t * val := mul_comm _ _
      linarith
  obtain ⟨pi, hpi⟩ := hsol
  have hfeas : ∀ j, Matrix.mulVec Mᵀ pi j ≤ dv j := by
    intro j
    have h := hpi (Sum.inr j)
    rw [hBrowS] at h
    have he : cc (Sum.inr j) = dv j := by simp [hcc]
    rwa [he] at h
  have hge : val ≤ dotProduct g pi := by
    have h := hpi (Sum.inl ())
    rw [hBrow0] at h
    have h0 : cc (Sum.inl ()) = -val := by simp [hcc]
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
  have hnn : ∀ k ∈ (Finset.univ : Finset ν),
      0 ≤ u0 k * (dv k - Matrix.mulVec Mᵀ pi k) := by
    intro k _
    have := hfeas k
    exact mul_nonneg (hu0 k) (by linarith)
  exact (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hcssum j (Finset.mem_univ j)

end LPGen

namespace LPGen

variable {ν κ : Type*} [Fintype ν] [Fintype κ] [DecidableEq ν] [DecidableEq κ]

/-- The augmented column `(q j, W_{·j})` in `Unit ⊕ ν`-indexed space. -/
noncomputable def augCol (W : Matrix ν κ ℝ) (q : κ → ℝ) (j : κ) : Unit ⊕ ν → ℝ :=
  Sum.elim (fun _ => q j) (fun i => W i j)

lemma sum_augCol (W : Matrix ν κ ℝ) (q : κ → ℝ) (y : κ → ℝ) :
    ∑ j, y j • augCol W q j = Sum.elim (fun _ => dotProduct q y) (Matrix.mulVec W y) := by
  funext I
  rcases I with _ | i
  · simp only [Finset.sum_apply, Pi.smul_apply, augCol, Sum.elim_inl, smul_eq_mul, dotProduct]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  · simp only [Finset.sum_apply, Pi.smul_apply, augCol, Sum.elim_inr, smul_eq_mul,
      Matrix.mulVec, dotProduct]
    exact Finset.sum_congr rfl (fun j _ => by ring)

/-- **Attainment for a standard-form linear program** over arbitrary finite index types. -/
theorem lp_min_attained (W : Matrix ν κ ℝ) (q : κ → ℝ) (d : ν → ℝ)
    (hfeas : ∃ y : κ → ℝ, (∀ j, 0 ≤ y j) ∧ Matrix.mulVec W y = d)
    (hbdd : ∃ beta : ℝ, ∀ y : κ → ℝ, (∀ j, 0 ≤ y j) → Matrix.mulVec W y = d →
      beta ≤ dotProduct q y) :
    ∃ y0 : κ → ℝ, (∀ j, 0 ≤ y0 j) ∧ Matrix.mulVec W y0 = d ∧
      ∀ y : κ → ℝ, (∀ j, 0 ≤ y j) → Matrix.mulVec W y = d →
        dotProduct q y0 ≤ dotProduct q y := by
  classical
  set S : Set ℝ := {r : ℝ | ∃ y : κ → ℝ, (∀ j, 0 ≤ y j) ∧ Matrix.mulVec W y = d ∧
    dotProduct q y = r} with hS
  have hSeq : S = (fun r : ℝ => (Sum.elim (fun _ => r) d : Unit ⊕ ν → ℝ)) ⁻¹'
      ConeGen.coneSpan (augCol W q) := by
    ext r
    constructor
    · rintro ⟨y, hy, hWy, rfl⟩
      exact ⟨y, hy, by rw [sum_augCol, hWy]⟩
    · rintro ⟨y, hy, hz⟩
      rw [sum_augCol] at hz
      refine ⟨y, hy, ?_, ?_⟩
      · funext i
        have h := congrArg (fun f => f (Sum.inr i)) hz
        simpa using h
      · have h := congrArg (fun f => f (Sum.inl ())) hz
        simpa using h
  have hcont : Continuous (fun r : ℝ => (Sum.elim (fun _ => r) d : Unit ⊕ ν → ℝ)) := by
    refine continuous_pi (fun I => ?_)
    rcases I with _ | i
    · have he : (fun r : ℝ => (Sum.elim (fun _ => r) d : Unit ⊕ ν → ℝ) (Sum.inl ()))
          = fun r : ℝ => r := by funext r; simp
      rw [he]; exact continuous_id
    · simpa using continuous_const
  have hSclosed : IsClosed S := by
    rw [hSeq]
    exact (ConeGen.isClosed_coneSpan' _).preimage hcont
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

end LPGen

namespace ConeGen

variable {ν ι : Type*} [Fintype ν] [Fintype ι]

lemma dot_add_smul (q y g : ι → ℝ) (s : ℝ) :
    dotProduct q (fun j => y j + s * g j)
      = dotProduct q y + s * dotProduct q g := by
  simp only [dotProduct, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun j _ => by ring)

/-- An optimal nonnegative combination can be taken with linearly independent support:
the linear-programming refinement of conic Carathéodory. -/
lemma reduce_support_cost (v : ι → (ν → ℝ)) (q : ι → ℝ) :
    ∀ (N : ℕ) (y : ι → ℝ), (∀ j, 0 ≤ y j) →
      (∀ y' : ι → ℝ, (∀ j, 0 ≤ y' j) → (∑ j, y' j • v j) = ∑ j, y j • v j →
        dotProduct q y ≤ dotProduct q y') →
      {j | y j ≠ 0}.toFinset.card ≤ N →
      ∃ y0 : ι → ℝ, (∀ j, 0 ≤ y0 j) ∧ (∑ j, y0 j • v j) = ∑ j, y j • v j ∧
        dotProduct q y0 = dotProduct q y ∧ LinearIndepOn ℝ v {j | y0 j ≠ 0} := by
  classical
  intro N
  induction N with
  | zero =>
      intro y hy _ hcard
      refine ⟨y, hy, rfl, rfl, ?_⟩
      have h0 : {j | y j ≠ 0}.toFinset = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hcard)
      have he : {j : ι | y j ≠ 0} = ∅ := by
        ext j
        constructor
        · intro hj
          have : j ∈ {j | y j ≠ 0}.toFinset := by simpa using hj
          simp [h0] at this
        · intro hj; exact absurd hj (Set.notMem_empty j)
      rw [he]
      exact linearIndepOn_empty ℝ v
  | succ N ih =>
      intro y hy hopt hcard
      by_cases hindep : LinearIndepOn ℝ v {j | y j ≠ 0}
      · exact ⟨y, hy, rfl, rfl, hindep⟩
      · set S : Finset ι := {j | y j ≠ 0}.toFinset with hS
        have hSset : (S : Set ι) = {j | y j ≠ 0} := by simp [hS]
        have hdep : ¬ LinearIndepOn ℝ v (S : Set ι) := by rwa [hSset]
        obtain ⟨f, hf0, j1, hj1S, hj1⟩ := not_linearIndepOn_finset_iff.mp hdep
        set g : ι → ℝ := fun j => if j ∈ S then f j else 0 with hg
        have hgsum : ∑ j, g j • v j = 0 := by
          have e1 : ∑ j, g j • v j = ∑ j ∈ S, g j • v j :=
            (Finset.sum_subset (Finset.subset_univ S) (fun j _ hj => by simp [hg, hj])).symm
          rw [e1, ← hf0]
          exact Finset.sum_congr rfl (fun j hj => by simp [hg, hj])
        have hgsupp : ∀ j, g j ≠ 0 → j ∈ S := by
          intro j hj; by_contra h; simp [hg, h] at hj
        have hgne : ∃ j, g j ≠ 0 := ⟨j1, by simpa [hg, hj1S] using hj1⟩
        set P : Finset ι := Finset.univ.filter (fun j => g j ≠ 0) with hP
        have hPne : P.Nonempty := by
          obtain ⟨j, hj⟩ := hgne
          exact ⟨j, by simp [hP, hj]⟩
        obtain ⟨jm, hjmP, hjmmin⟩ := P.exists_min_image (fun j => y j / |g j|) hPne
        have hgjm : g jm ≠ 0 := by simpa [hP] using hjmP
        have hyjm : 0 < y jm := by
          have hmem : jm ∈ S := hgsupp jm hgjm
          have : y jm ≠ 0 := by
            have : jm ∈ {j | y j ≠ 0} := by rw [← hSset]; exact_mod_cast hmem
            exact this
          exact lt_of_le_of_ne (hy jm) (Ne.symm this)
        set t0 : ℝ := y jm / |g jm| with ht0
        have ht0pos : 0 < t0 := div_pos hyjm (abs_pos.mpr hgjm)
        have hpm : ∀ s : ℝ, |s| ≤ t0 → ∀ j, 0 ≤ y j + s * g j := by
          intro s hs j
          by_cases hgj : g j = 0
          · simp [hgj]; exact hy j
          · have hjP : j ∈ P := by simp [hP, hgj]
            have hmin := hjmmin j hjP
            have habs : |s * g j| ≤ y j := by
              rw [abs_mul]
              calc |s| * |g j| ≤ t0 * |g j| :=
                    mul_le_mul_of_nonneg_right hs (abs_nonneg _)
                _ ≤ (y j / |g j|) * |g j| :=
                    mul_le_mul_of_nonneg_right hmin (abs_nonneg _)
                _ = y j := div_mul_cancel₀ _ (abs_ne_zero.mpr hgj)
            have h2 := neg_abs_le (s * g j)
            linarith
        have hfeas_pm : ∀ s : ℝ, (∑ j, (y j + s * g j) • v j) = ∑ j, y j • v j := by
          intro s
          have : ∑ j, (y j + s * g j) • v j = (∑ j, y j • v j) + s • ∑ j, g j • v j := by
            rw [Finset.smul_sum, ← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl (fun j _ => ?_)
            simp only [add_smul, smul_smul]
          rw [this, hgsum, smul_zero, add_zero]
        have hqg : dotProduct q g = 0 := by
          have h1 := hopt (fun j => y j + t0 * g j) (hpm t0 (by rw [abs_of_pos ht0pos]))
            (hfeas_pm t0)
          have h2 := hopt (fun j => y j + (-t0) * g j)
            (hpm (-t0) (by rw [abs_neg, abs_of_pos ht0pos])) (hfeas_pm (-t0))
          rw [dot_add_smul] at h1 h2
          have hp1 : 0 ≤ t0 * dotProduct q g := by linarith
          have hp2 : 0 ≤ (-t0) * dotProduct q g := by linarith
          nlinarith [ht0pos]
        -- normalise so that some coordinate is positive
        obtain ⟨mu, hmusum, hmusupp, hmuq, j0, hj0pos⟩ :
            ∃ mu : ι → ℝ, (∑ j, mu j • v j = 0) ∧ (∀ j, mu j ≠ 0 → j ∈ S) ∧
              dotProduct q mu = 0 ∧ ∃ j0, 0 < mu j0 := by
          obtain ⟨j, hj⟩ := hgne
          rcases lt_or_gt_of_ne hj with hneg | hpos
          · refine ⟨fun k => -g k, ?_, ?_, ?_, j, by linarith⟩
            · simp only [neg_smul, Finset.sum_neg_distrib, hgsum, neg_zero]
            · intro k hk; exact hgsupp k (by simpa using fun h => hk (by simp [h]))
            · have hqg' : ∑ x, q x * g x = 0 := by simpa [dotProduct] using hqg
              simp only [dotProduct, mul_neg]
              rw [Finset.sum_neg_distrib, hqg', neg_zero]
          · exact ⟨g, hgsum, hgsupp, hqg, j, hpos⟩
        set P2 : Finset ι := Finset.univ.filter (fun j => 0 < mu j) with hP2
        have hP2ne : P2.Nonempty := ⟨j0, by simp [hP2, hj0pos]⟩
        obtain ⟨jn, hjnP2, hjnmin⟩ := P2.exists_min_image (fun j => y j / mu j) hP2ne
        set t : ℝ := y jn / mu jn with ht
        have hmujn : 0 < mu jn := by simpa [hP2] using hjnP2
        have ht0' : 0 ≤ t := div_nonneg (hy jn) hmujn.le
        set y' : ι → ℝ := fun j => y j - t * mu j with hy'
        have hy'nonneg : ∀ j, 0 ≤ y' j := by
          intro j
          by_cases hmj : 0 < mu j
          · have hjP : j ∈ P2 := by simp [hP2, hmj]
            have hmin := hjnmin j hjP
            have h2 : t * mu j ≤ (y j / mu j) * mu j :=
              mul_le_mul_of_nonneg_right hmin hmj.le
            rw [div_mul_cancel₀ _ (ne_of_gt hmj)] at h2
            simp only [hy']; linarith
          · have hmj' : mu j ≤ 0 := le_of_not_gt hmj
            have : t * mu j ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ht0' hmj'
            simp only [hy']; linarith [hy j]
        have hy'jn : y' jn = 0 := by
          simp only [hy', ht, div_mul_cancel₀ _ (ne_of_gt hmujn), sub_self]
        have hy'sum : ∑ j, y' j • v j = ∑ j, y j • v j := by
          have hrw : ∀ j, y' j = y j + (-t) * mu j := by intro j; simp only [hy']; ring
          have := hfeas_pm
          calc ∑ j, y' j • v j = ∑ j, (y j + (-t) * mu j) • v j := by
                exact Finset.sum_congr rfl (fun j _ => by rw [hrw j])
            _ = (∑ j, y j • v j) + (-t) • ∑ j, mu j • v j := by
                rw [Finset.smul_sum, ← Finset.sum_add_distrib]
                refine Finset.sum_congr rfl (fun j _ => ?_)
                simp only [add_smul, smul_smul]
            _ = ∑ j, y j • v j := by rw [hmusum, smul_zero, add_zero]
        have hy'q : dotProduct q y' = dotProduct q y := by
          have hrw : y' = fun j => y j + (-t) * mu j := by
            funext j; simp only [hy']; ring
          rw [hrw, dot_add_smul, hmuq]
          ring
        have hy'opt : ∀ y'' : ι → ℝ, (∀ j, 0 ≤ y'' j) →
            (∑ j, y'' j • v j) = ∑ j, y' j • v j → dotProduct q y' ≤ dotProduct q y'' := by
          intro y'' h1 h2
          rw [hy'q]
          exact hopt y'' h1 (by rw [h2, hy'sum])
        have hsupp' : {j | y' j ≠ 0}.toFinset ⊆ S.erase jn := by
          intro j hj
          simp only [Set.mem_toFinset, Set.mem_setOf_eq] at hj
          refine Finset.mem_erase.mpr ⟨?_, ?_⟩
          · rintro rfl; exact hj hy'jn
          · by_contra hjS
            have hyj : y j = 0 := by by_contra h; exact hjS (by simp [hS, h])
            have hmuj : mu j = 0 := by by_contra h; exact hjS (hmusupp j h)
            exact hj (by simp [hy', hyj, hmuj])
        have hcard' : {j | y' j ≠ 0}.toFinset.card ≤ N := by
          have h1 : {j | y' j ≠ 0}.toFinset.card ≤ (S.erase jn).card :=
            Finset.card_le_card hsupp'
          have hjnS : jn ∈ S := hmusupp jn (ne_of_gt hmujn)
          have h2 : (S.erase jn).card = S.card - 1 := Finset.card_erase_of_mem hjnS
          have h3 : 1 ≤ S.card := Finset.card_pos.mpr ⟨jn, hjnS⟩
          omega
        obtain ⟨y0, h1, h2, h3, h4⟩ := ih y' hy'nonneg hy'opt hcard'
        exact ⟨y0, h1, by rw [h2, hy'sum], by rw [h3, hy'q], h4⟩

end ConeGen

namespace ConeGen

variable {ν ι : Type*} [Fintype ν] [Fintype ι] [DecidableEq ν] [DecidableEq ι]

lemma mat_of_family (v : ι → (ν → ℝ)) (y : ι → ℝ) :
    Matrix.mulVec (Matrix.of (fun (i : ν) (j : ι) => v j i)) y = ∑ j, y j • v j := by
  funext i
  simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul]
  exact Finset.sum_congr rfl (fun j _ => by ring)

/-- Attainment for a linear program written with an explicit family of columns. -/
lemma min_attained_family (v : ι → (ν → ℝ)) (c : ι → ℝ) (d : ν → ℝ)
    (hfeas : ∃ y : ι → ℝ, (∀ j, 0 ≤ y j) ∧ ∑ j, y j • v j = d)
    (hbdd : ∃ beta : ℝ, ∀ y : ι → ℝ, (∀ j, 0 ≤ y j) → (∑ j, y j • v j = d) →
      beta ≤ dotProduct c y) :
    ∃ y0 : ι → ℝ, (∀ j, 0 ≤ y0 j) ∧ (∑ j, y0 j • v j = d) ∧
      ∀ y : ι → ℝ, (∀ j, 0 ≤ y j) → (∑ j, y j • v j = d) →
        dotProduct c y0 ≤ dotProduct c y := by
  have h := LPGen.lp_min_attained (Matrix.of (fun (i : ν) (j : ι) => v j i)) c d
    (by obtain ⟨y, hy, he⟩ := hfeas; exact ⟨y, hy, by rw [mat_of_family]; exact he⟩)
    (by
      obtain ⟨beta, hb⟩ := hbdd
      refine ⟨beta, fun y hy he => hb y hy ?_⟩
      rw [← mat_of_family]; exact he)
  obtain ⟨y0, h1, h2, h3⟩ := h
  refine ⟨y0, h1, by rw [← mat_of_family]; exact h2, ?_⟩
  intro y hy he
  exact h3 y hy (by rw [mat_of_family]; exact he)

/-- An optimal solution with linearly independent support columns. -/
lemma min_attained_basic_family (v : ι → (ν → ℝ)) (c : ι → ℝ) (d : ν → ℝ)
    (hfeas : ∃ y : ι → ℝ, (∀ j, 0 ≤ y j) ∧ ∑ j, y j • v j = d)
    (hbdd : ∃ beta : ℝ, ∀ y : ι → ℝ, (∀ j, 0 ≤ y j) → (∑ j, y j • v j = d) →
      beta ≤ dotProduct c y) :
    ∃ y0 : ι → ℝ, (∀ j, 0 ≤ y0 j) ∧ (∑ j, y0 j • v j = d) ∧
      (∀ y : ι → ℝ, (∀ j, 0 ≤ y j) → (∑ j, y j • v j = d) →
        dotProduct c y0 ≤ dotProduct c y) ∧
      LinearIndepOn ℝ v {j | y0 j ≠ 0} := by
  classical
  obtain ⟨y, hy, hfe, hmin⟩ := min_attained_family v c d hfeas hbdd
  obtain ⟨y0, h1, h2, h3, h4⟩ :=
    reduce_support_cost v c {j | y j ≠ 0}.toFinset.card y hy
      (fun y' hy' hfe' => hmin y' hy' (by rw [hfe'] at *; exact hfe)) le_rfl
  refine ⟨y0, h1, by rw [h2, hfe], ?_, h4⟩
  intro y' hy' hfe'
  rw [h3]
  exact hmin y' hy' hfe'

/-- Basic solutions of a fixed system form a finite set: each is determined by its support. -/
lemma finite_basic_family (v : ι → (ν → ℝ)) (d : ν → ℝ) :
    {y : ι → ℝ | (∑ j, y j • v j = d) ∧ LinearIndepOn ℝ v {j | y j ≠ 0}}.Finite := by
  classical
  refine Set.Finite.of_finite_image (f := fun y : ι → ℝ => {j | y j ≠ 0}.toFinset)
    (Set.toFinite _) ?_
  rintro y1 ⟨he1, hi1⟩ y2 ⟨he2, hi2⟩ hsupp
  have hzero : ∑ j, (y1 j - y2 j) • v j = 0 := by
    have : ∑ j, (y1 j - y2 j) • v j = (∑ j, y1 j • v j) - ∑ j, y2 j • v j := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun j _ => by rw [sub_smul])
    rw [this, he1, he2, sub_self]
  set S : Finset ι := {j | y1 j ≠ 0}.toFinset with hS
  have hoff : ∀ j, j ∉ S → y1 j - y2 j = 0 := by
    intro j hj
    have h1 : y1 j = 0 := by
      by_contra h; exact hj (by simp [hS, h])
    have h2 : y2 j = 0 := by
      by_contra h
      have hmem : j ∈ {j | y2 j ≠ 0}.toFinset := by simp [h]
      have hsupp' : {j | y1 j ≠ 0}.toFinset = {j | y2 j ≠ 0}.toFinset := hsupp
      rw [← hsupp'] at hmem
      exact hj hmem
    rw [h1, h2, sub_self]
  have hSsum : ∑ j ∈ S, (y1 j - y2 j) • v j = 0 := by
    rw [Finset.sum_subset (Finset.subset_univ S) (fun j _ hj => by rw [hoff j hj, zero_smul])]
    exact hzero
  have hind : LinearIndepOn ℝ v (S : Set ι) := by
    have : (S : Set ι) = {j | y1 j ≠ 0} := by simp [hS]
    rw [this]; exact hi1
  have hon := linearIndepOn_finset_iff.mp hind (fun j => y1 j - y2 j) hSsum
  funext j
  by_cases hj : j ∈ S
  · have := hon j hj; linarith
  · have := hoff j hj; linarith

end ConeGen

namespace LPDual

open Matrix

variable {ν κ : Type*} [Fintype ν] [Fintype κ] [DecidableEq ν] [DecidableEq κ]

/-- Columns of the dual `max πᵀd, Wᵀπ ≤ q` rewritten in standard form with
`π = π⁺ - π⁻` and a slack. -/
noncomputable def dualCols (W : Matrix ν κ ℝ) : ((ν ⊕ ν) ⊕ κ) → (κ → ℝ) :=
  fun t =>
    match t with
    | Sum.inl (Sum.inl a) => fun j => W a j
    | Sum.inl (Sum.inr a) => fun j => -(W a j)
    | Sum.inr j0 => Pi.single j0 1

/-- The dual vector carried by a standard-form point. -/
def piOf (z : ((ν ⊕ ν) ⊕ κ) → ℝ) : ν → ℝ :=
  fun a => z (Sum.inl (Sum.inl a)) - z (Sum.inl (Sum.inr a))

/-- Cost vector of the standard form of the dual. -/
def dualCost (d : ν → ℝ) : ((ν ⊕ ν) ⊕ κ) → ℝ :=
  fun t =>
    match t with
    | Sum.inl (Sum.inl a) => -d a
    | Sum.inl (Sum.inr a) => d a
    | Sum.inr _ => 0

lemma dual_sum_apply (W : Matrix ν κ ℝ) (z : ((ν ⊕ ν) ⊕ κ) → ℝ) (j : κ) :
    (∑ t, z t • dualCols W t) j
      = Matrix.mulVec (Matrix.transpose W) (piOf z) j + z (Sum.inr j) := by
  classical
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  have h3 : ∑ j0 : κ, z (Sum.inr j0) * (dualCols W (Sum.inr j0)) j = z (Sum.inr j) := by
    simp only [dualCols, Pi.single_apply, mul_ite, mul_one, mul_zero]
    simp
  rw [h3]
  congr 1
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, piOf, dualCols]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun a _ => by ring)

lemma dualCost_dot (d : ν → ℝ) (z : ((ν ⊕ ν) ⊕ κ) → ℝ) :
    dotProduct (dualCost d) z = - dotProduct d (piOf z) := by
  simp only [dotProduct, dualCost, piOf]
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr]
  rw [← Finset.sum_neg_distrib]
  have h0 : ∑ _j : κ, (0 : ℝ) * z (Sum.inr _j) = 0 := by simp
  rw [h0, add_zero, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun a _ => by ring)

/-- Standard-form feasibility of the dual is exactly dual feasibility. -/
lemma dual_feas_of (W : Matrix ν κ ℝ) (q : κ → ℝ) (z : ((ν ⊕ ν) ⊕ κ) → ℝ)
    (hz : ∀ t, 0 ≤ z t) (hsum : ∑ t, z t • dualCols W t = q) :
    ∀ j, Matrix.mulVec (Matrix.transpose W) (piOf z) j ≤ q j := by
  intro j
  have h := congrArg (fun f => f j) hsum
  rw [dual_sum_apply] at h
  have hnn := hz (Sum.inr j)
  linarith

lemma exists_dual_std (W : Matrix ν κ ℝ) (q : κ → ℝ) (pi : ν → ℝ)
    (hpi : ∀ j, Matrix.mulVec (Matrix.transpose W) pi j ≤ q j) :
    ∃ z : ((ν ⊕ ν) ⊕ κ) → ℝ, (∀ t, 0 ≤ z t) ∧ (∑ t, z t • dualCols W t = q) ∧
      piOf z = pi := by
  classical
  refine ⟨fun t =>
    match t with
    | Sum.inl (Sum.inl a) => max (pi a) 0
    | Sum.inl (Sum.inr a) => max (-(pi a)) 0
    | Sum.inr j => q j - Matrix.mulVec (Matrix.transpose W) pi j, ?_, ?_, ?_⟩
  · rintro ((a | a) | j)
    · exact le_max_right _ _
    · exact le_max_right _ _
    · simpa using sub_nonneg.mpr (hpi _)
  · funext j
    rw [dual_sum_apply]
    have hpieq : piOf (fun t =>
        match t with
        | Sum.inl (Sum.inl a) => max (pi a) 0
        | Sum.inl (Sum.inr a) => max (-(pi a)) 0
        | Sum.inr j => q j - Matrix.mulVec (Matrix.transpose W) pi j) = pi := by
      funext a
      simp only [piOf]
      rcases le_or_gt 0 (pi a) with h | h
      · rw [max_eq_left h, max_eq_right (by linarith)]; ring
      · rw [max_eq_right (by linarith), max_eq_left (by linarith)]; ring
    rw [hpieq]
    simp
  · funext a
    simp only [piOf]
    rcases le_or_gt 0 (pi a) with h | h
    · rw [max_eq_left h, max_eq_right (by linarith)]; ring
    · rw [max_eq_right (by linarith), max_eq_left (by linarith)]; ring

end LPDual

namespace LPDual

open Matrix

variable {ν κ : Type*} [Fintype ν] [Fintype κ] [DecidableEq ν] [DecidableEq κ]

/-- There is a finite set of dual-feasible vectors that contains an optimal one for every
objective for which the dual is bounded above: the basic feasible solutions of the dual,
which depend only on `W` and `q`. -/
theorem exists_dual_candidates (W : Matrix ν κ ℝ) (q : κ → ℝ) :
    ∃ V : Set (ν → ℝ), V.Finite ∧
      (∀ pi ∈ V, ∀ j, Matrix.mulVec (Matrix.transpose W) pi j ≤ q j) ∧
      ∀ d : ν → ℝ,
        (∃ pi : ν → ℝ, ∀ j, Matrix.mulVec (Matrix.transpose W) pi j ≤ q j) →
        (∃ B : ℝ, ∀ pi : ν → ℝ,
          (∀ j, Matrix.mulVec (Matrix.transpose W) pi j ≤ q j) → dotProduct d pi ≤ B) →
        ∃ pi0 ∈ V, ∀ pi : ν → ℝ,
          (∀ j, Matrix.mulVec (Matrix.transpose W) pi j ≤ q j) →
            dotProduct d pi ≤ dotProduct d pi0 := by
  classical
  set Basic : Set (((ν ⊕ ν) ⊕ κ) → ℝ) :=
    {z | (∀ t, 0 ≤ z t) ∧ (∑ t, z t • dualCols W t = q) ∧
      LinearIndepOn ℝ (dualCols W) {t | z t ≠ 0}} with hBasic
  have hBfin : Basic.Finite := by
    refine Set.Finite.subset (ConeGen.finite_basic_family (dualCols W) q) ?_
    rintro z ⟨_, h2, h3⟩
    exact ⟨h2, h3⟩
  refine ⟨piOf '' Basic, hBfin.image _, ?_, ?_⟩
  · rintro pi ⟨z, ⟨hz1, hz2, _⟩, rfl⟩
    exact dual_feas_of W q z hz1 hz2
  · rintro d ⟨pi1, hpi1⟩ ⟨B, hB⟩
    obtain ⟨z1, hz1nn, hz1sum, hz1pi⟩ := exists_dual_std W q pi1 hpi1
    have hbdd : ∃ beta : ℝ, ∀ z : ((ν ⊕ ν) ⊕ κ) → ℝ, (∀ t, 0 ≤ z t) →
        (∑ t, z t • dualCols W t = q) → beta ≤ dotProduct (dualCost d) z := by
      refine ⟨-B, ?_⟩
      intro z hz hsum
      rw [dualCost_dot]
      have := hB (piOf z) (dual_feas_of W q z hz hsum)
      linarith
    obtain ⟨z0, hz0nn, hz0sum, hz0min, hz0ind⟩ :=
      ConeGen.min_attained_basic_family (dualCols W) (dualCost d) q ⟨z1, hz1nn, hz1sum⟩ hbdd
    refine ⟨piOf z0, ⟨z0, ⟨hz0nn, hz0sum, hz0ind⟩, rfl⟩, ?_⟩
    intro pi hpi
    obtain ⟨z, hznn, hzsum, hzpi⟩ := exists_dual_std W q pi hpi
    have h := hz0min z hznn hzsum
    rw [dualCost_dot, dualCost_dot, hzpi] at h
    linarith

end LPDual

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


end StochasticProg.Recourse

namespace StochasticProg.Recourse

variable {n1 n2 m1 m2 K : ℕ}

/-- If every scenario term is bounded below by a real, so is `Q`. -/
lemma coe_sum_le_foldr_bookAdd : ∀ (N : ℕ) (a : Fin N → EReal) (r : Fin N → ℝ),
    (∀ k, ((r k : ℝ) : EReal) ≤ a k) →
    ((∑ k, r k : ℝ) : EReal) ≤ (List.ofFn a).foldr bookAdd 0 := by
  intro N
  induction N with
  | zero => intro a r _; simp
  | succ N ih =>
      intro a r h
      rw [List.ofFn_succ, List.foldr_cons, Fin.sum_univ_succ]
      by_cases hc : a 0 = ⊤ ∨ (List.ofFn fun i : Fin N => a i.succ).foldr bookAdd 0 = ⊤
      · rw [bookAdd, if_pos hc]; exact le_top
      · rw [bookAdd, if_neg hc, EReal.coe_add]
        exact add_le_add (h 0) (ih (fun i => a i.succ) (fun i => r i.succ) (fun i => h i.succ))

/-- If every scenario term is bounded above by a real, so is `Q`. -/
lemma foldr_bookAdd_le_coe_sum : ∀ (N : ℕ) (a : Fin N → EReal) (r : Fin N → ℝ),
    (∀ k, a k ≤ ((r k : ℝ) : EReal)) →
    (List.ofFn a).foldr bookAdd 0 ≤ ((∑ k, r k : ℝ) : EReal) := by
  intro N
  induction N with
  | zero => intro a r _; simp
  | succ N ih =>
      intro a r h
      rw [List.ofFn_succ, List.foldr_cons, Fin.sum_univ_succ]
      have hrest := ih (fun i => a i.succ) (fun i => r i.succ) (fun i => h i.succ)
      have h0 : a 0 ≠ ⊤ := fun hh => by
        have := h 0; rw [hh] at this
        exact (EReal.coe_ne_top (r 0)) (top_le_iff.mp this)
      have hr : (List.ofFn fun i : Fin N => a i.succ).foldr bookAdd 0 ≠ ⊤ := fun hh => by
        rw [hh] at hrest
        exact (EReal.coe_ne_top _) (top_le_iff.mp hrest)
      rw [bookAdd, if_neg (by tauto), EReal.coe_add]
      exact add_le_add (h 0) hrest

lemma Q_eq_foldr (inst : Instance n1 n2 m1 m2 K) (x : Fin n1 → ℝ) :
    Q inst x = (List.ofFn (fun k : Fin K => ((inst.p k : ℝ) : EReal) * QVal inst x k)).foldr
      bookAdd 0 := rfl

end StochasticProg.Recourse

namespace StochasticProg.Recourse

open scoped Classical

variable {n1 n2 m1 m2 K : ℕ}

lemma foldr_bookAdd_ne_bot (l : List EReal) (h : ∀ a ∈ l, a ≠ ⊥) :
    l.foldr bookAdd 0 ≠ ⊥ := by
  induction l with
  | nil => simp
  | cons a l ih =>
      rw [List.foldr_cons, bookAdd]
      by_cases hc : a = ⊤ ∨ l.foldr bookAdd 0 = ⊥ ∨ True
      · by_cases hc2 : a = ⊤ ∨ l.foldr bookAdd 0 = ⊤
        · rw [if_pos hc2]; exact top_ne_bot
        · rw [if_neg hc2]
          exact EReal.add_ne_bot_iff.mpr
            ⟨h a (by simp), ih (fun b hb => h b (by simp [hb]))⟩
      · exact absurd (Or.inr (Or.inr trivial)) hc

lemma scenario_term_ne_bot (inst : Instance n1 n2 m1 m2 K)
    (hQb : ∀ x k, QVal inst x k ≠ ⊥) (x : Fin n1 → ℝ) (k : Fin K) :
    ((inst.p k : ℝ) : EReal) * QVal inst x k ≠ ⊥ := by
  rw [ne_eq, EReal.mul_eq_bot]
  push_neg
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h; exact absurd h (EReal.coe_ne_bot _)
  · intro _; exact hQb x k
  · intro h; exact absurd h (EReal.coe_ne_top _)
  · intro h
    exact absurd h (not_lt.mpr (by exact_mod_cast inst.hp_nonneg k))

lemma Q_ne_bot (inst : Instance n1 n2 m1 m2 K) (hQb : ∀ x k, QVal inst x k ≠ ⊥)
    (x : Fin n1 → ℝ) : Q inst x ≠ ⊥ := by
  rw [Q_eq_foldr]
  refine foldr_bookAdd_ne_bot _ (fun a ha => ?_)
  obtain ⟨k, rfl⟩ := List.mem_ofFn.mp ha
  exact scenario_term_ne_bot inst hQb x k

end StochasticProg.Recourse

namespace StochasticProg.Recourse

open scoped Classical

variable {n1 n2 m1 m2 K : ℕ}

/-- At a point of `K2` each scenario of positive probability is feasible. -/
lemma feasible_of_K2 (inst : Instance n1 n2 m1 m2 K) {x : Fin n1 → ℝ} (hx : x ∈ K2 inst)
    {k : Fin K} (hp : 0 < inst.p k) :
    ∃ y : Fin n2 → ℝ, (∀ l, 0 ≤ y l) ∧
      Matrix.mulVec inst.W y = inst.h k - Matrix.mulVec (inst.T k) x :=
  (QVal_ne_top_iff inst x k).mp
    ((QVal_ne_top_iff inst x k).mpr
      ((scenario_term_ne_top_iff inst x k).mp ((Q_ne_top_iff inst x).mp hx k) hp))

/-- The scenario value is a real number at a point of `K2`. -/
lemma QVal_eq_coe (inst : Instance n1 n2 m1 m2 K) (hQb : ∀ x k, QVal inst x k ≠ ⊥)
    {x : Fin n1 → ℝ} (hx : x ∈ K2 inst) {k : Fin K} (hp : 0 < inst.p k) :
    QVal inst x k = (((QVal inst x k).toReal : ℝ) : EReal) := by
  have htop : QVal inst x k ≠ ⊤ :=
    (QVal_ne_top_iff inst x k).mpr
      ((scenario_term_ne_top_iff inst x k).mp ((Q_ne_top_iff inst x).mp hx k) hp)
  exact (EReal.coe_toReal htop (hQb x k)).symm

/-- Weak duality for a scenario problem. -/
lemma weak_duality_scen (inst : Instance n1 n2 m1 m2 K) (k : Fin K) (pi : Fin m2 → ℝ)
    (hpi : ∀ l, Matrix.mulVec (Matrix.transpose inst.W) pi l ≤ inst.q k l)
    (x : Fin n1 → ℝ) :
    ((dotProduct pi (inst.h k - Matrix.mulVec (inst.T k) x) : ℝ) : EReal)
      ≤ QVal inst x k := by
  rw [QVal]
  refine le_sInf ?_
  rintro z ⟨y, hy, hWy, rfl⟩
  have h1 : dotProduct pi (inst.h k - Matrix.mulVec (inst.T k) x)
      = dotProduct (Matrix.mulVec (Matrix.transpose inst.W) pi) y := by
    rw [← hWy, Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec]
  have h2 : dotProduct (Matrix.mulVec (Matrix.transpose inst.W) pi) y
      ≤ dotProduct (inst.q k) y :=
    Finset.sum_le_sum (fun l _ => mul_le_mul_of_nonneg_right (hpi l) (hy l))
  rw [h1]
  exact_mod_cast le_trans h2 (le_refl _)

/-- At a point of `K2` the scenario minimum is attained. -/
lemma scen_attained (inst : Instance n1 n2 m1 m2 K) (hQb : ∀ x k, QVal inst x k ≠ ⊥)
    {x : Fin n1 → ℝ} (hx : x ∈ K2 inst) {k : Fin K} (hp : 0 < inst.p k) :
    ∃ y : Fin n2 → ℝ, (∀ l, 0 ≤ y l) ∧
      Matrix.mulVec inst.W y = inst.h k - Matrix.mulVec (inst.T k) x ∧
      QVal inst x k = ((dotProduct (inst.q k) y : ℝ) : EReal) ∧
      ∀ y' : Fin n2 → ℝ, (∀ l, 0 ≤ y' l) →
        Matrix.mulVec inst.W y' = inst.h k - Matrix.mulVec (inst.T k) x →
        dotProduct (inst.q k) y ≤ dotProduct (inst.q k) y' := by
  have hVeq := QVal_eq_coe inst hQb hx hp
  have hbdd : ∃ beta : ℝ, ∀ y : Fin n2 → ℝ, (∀ l, 0 ≤ y l) →
      Matrix.mulVec inst.W y = inst.h k - Matrix.mulVec (inst.T k) x →
      beta ≤ dotProduct (inst.q k) y := by
    refine ⟨(QVal inst x k).toReal, ?_⟩
    intro y hy hWy
    have hmem : ((dotProduct (inst.q k) y : ℝ) : EReal) ∈
        {z : EReal | ∃ yy : Fin n2 → ℝ, (∀ i, 0 ≤ yy i) ∧
          Matrix.mulVec inst.W yy = inst.h k - Matrix.mulVec (inst.T k) x ∧
          z = ((dotProduct (inst.q k) yy : ℝ) : EReal)} := ⟨y, hy, hWy, rfl⟩
    have hle : QVal inst x k ≤ ((dotProduct (inst.q k) y : ℝ) : EReal) := sInf_le hmem
    rw [hVeq] at hle
    exact_mod_cast hle
  obtain ⟨y0, hy0, hW0, hmin⟩ :=
    LPGen.lp_min_attained inst.W (inst.q k) (inst.h k - Matrix.mulVec (inst.T k) x)
      (feasible_of_K2 inst hx hp) hbdd
  refine ⟨y0, hy0, hW0, ?_, hmin⟩
  have h1 : QVal inst x k ≤ ((dotProduct (inst.q k) y0 : ℝ) : EReal) :=
    sInf_le ⟨y0, hy0, hW0, rfl⟩
  have h2 : ((dotProduct (inst.q k) y0 : ℝ) : EReal) ≤ QVal inst x k := by
    rw [QVal]
    refine le_sInf ?_
    rintro z ⟨yy, hyy, hWyy, rfl⟩
    exact_mod_cast hmin yy hyy hWyy
  exact le_antisymm h1 h2

/-- Strong duality for a scenario problem at a point of `K2`. -/
lemma strong_duality_scen (inst : Instance n1 n2 m1 m2 K) (hQb : ∀ x k, QVal inst x k ≠ ⊥)
    {x : Fin n1 → ℝ} (hx : x ∈ K2 inst) {k : Fin K} (hp : 0 < inst.p k) :
    ∃ pi : Fin m2 → ℝ, (∀ l, Matrix.mulVec (Matrix.transpose inst.W) pi l ≤ inst.q k l) ∧
      QVal inst x k
        = ((dotProduct pi (inst.h k - Matrix.mulVec (inst.T k) x) : ℝ) : EReal) := by
  obtain ⟨y0, hy0, hW0, hval, hmin⟩ := scen_attained inst hQb hx hp
  obtain ⟨pi, hpi, hvaleq, _⟩ :=
    LPGen.lp_strong_duality inst.W (inst.q k) (inst.h k - Matrix.mulVec (inst.T k) x)
      y0 hy0 hW0 hmin
  refine ⟨pi, hpi, ?_⟩
  rw [hval, ← hvaleq, dotProduct_comm]

end StochasticProg.Recourse

namespace StochasticProg.Recourse

open scoped Classical

variable {n1 n2 m1 m2 K : ℕ}

/-- A finite set of dual vectors realising the scenario value at every point of `K2`. -/
lemma scen_dual_candidates (inst : Instance n1 n2 m1 m2 K)
    (hQb : ∀ x k, QVal inst x k ≠ ⊥) (k : Fin K) (hp : 0 < inst.p k) :
    ∃ V : Set (Fin m2 → ℝ), V.Finite ∧
      (∀ pi ∈ V, ∀ l, Matrix.mulVec (Matrix.transpose inst.W) pi l ≤ inst.q k l) ∧
      ∀ x ∈ K2 inst, ∃ pi ∈ V,
        QVal inst x k
          = ((dotProduct pi (inst.h k - Matrix.mulVec (inst.T k) x) : ℝ) : EReal) := by
  obtain ⟨V, hVfin, hVfeas, hVopt⟩ := LPDual.exists_dual_candidates inst.W (inst.q k)
  refine ⟨V, hVfin, hVfeas, ?_⟩
  intro x hx
  obtain ⟨pis, hpis, hpisval⟩ := strong_duality_scen inst hQb hx hp
  obtain ⟨y, hy, hWy⟩ := feasible_of_K2 inst hx hp
  have hB : ∃ B : ℝ, ∀ pi : Fin m2 → ℝ,
      (∀ l, Matrix.mulVec (Matrix.transpose inst.W) pi l ≤ inst.q k l) →
      dotProduct (inst.h k - Matrix.mulVec (inst.T k) x) pi ≤ B := by
    refine ⟨dotProduct (inst.q k) y, ?_⟩
    intro pi hpi
    have h1 : dotProduct (inst.h k - Matrix.mulVec (inst.T k) x) pi
        = dotProduct (Matrix.mulVec (Matrix.transpose inst.W) pi) y := by
      rw [dotProduct_comm, ← hWy, Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec]
    rw [h1]
    exact Finset.sum_le_sum (fun l _ => mul_le_mul_of_nonneg_right (hpi l) (hy l))
  obtain ⟨pi0, hpi0V, hpi0opt⟩ :=
    hVopt (inst.h k - Matrix.mulVec (inst.T k) x) ⟨pis, hpis⟩ hB
  refine ⟨pi0, hpi0V, le_antisymm ?_ (weak_duality_scen inst k pi0 (hVfeas pi0 hpi0V) x)⟩
  have h1 := hpi0opt pis hpis
  rw [hpisval]
  rw [dotProduct_comm (inst.h k - Matrix.mulVec (inst.T k) x) pis,
    dotProduct_comm (inst.h k - Matrix.mulVec (inst.T k) x) pi0] at h1
  exact_mod_cast h1

/-- The scenario value function is Lipschitz on `K2`, one-sided form. -/
lemma scen_lipschitz (inst : Instance n1 n2 m1 m2 K)
    (hQb : ∀ x k, QVal inst x k ≠ ⊥) (k : Fin K) (hp : 0 < inst.p k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ K2 inst, ∀ x' ∈ K2 inst,
      (QVal inst x k).toReal - (QVal inst x' k).toReal ≤ C * dist x x' := by
  obtain ⟨V, hVfin, hVfeas, hVrep⟩ := scen_dual_candidates inst hQb k hp
  set F : (Fin m2 → ℝ) → ℝ := fun pi => ∑ i, ∑ j, |pi i| * |inst.T k i j| with hF
  obtain ⟨C0, hC0⟩ := (hVfin.image F).bddAbove
  refine ⟨max C0 0, le_max_right _ _, ?_⟩
  intro x hx x' hx'
  obtain ⟨pi, hpiV, hpival⟩ := hVrep x hx
  have hxr : (QVal inst x k).toReal
      = dotProduct pi (inst.h k - Matrix.mulVec (inst.T k) x) := by
    rw [hpival]; exact EReal.toReal_coe _
  have hx'ge := weak_duality_scen inst k pi (hVfeas pi hpiV) x'
  rw [QVal_eq_coe inst hQb hx' hp] at hx'ge
  have hx'r : dotProduct pi (inst.h k - Matrix.mulVec (inst.T k) x')
      ≤ (QVal inst x' k).toReal := by exact_mod_cast hx'ge
  have hcoord : ∀ j, |x' j - x j| ≤ dist x x' := by
    intro j
    have h := dist_le_pi_dist x x' j
    rw [Real.dist_eq] at h
    rw [abs_sub_comm]
    exact h
  have hval : dotProduct pi (inst.h k - Matrix.mulVec (inst.T k) x)
      - dotProduct pi (inst.h k - Matrix.mulVec (inst.T k) x')
      = ∑ i, pi i * (∑ j, inst.T k i j * (x' j - x j)) := by
    simp only [dotProduct, Pi.sub_apply]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    have e : Matrix.mulVec (inst.T k) x' i - Matrix.mulVec (inst.T k) x i
        = ∑ j, inst.T k i j * (x' j - x j) := by
      simp only [Matrix.mulVec, dotProduct]
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun j _ => by ring)
    rw [← e]; ring
  have hb1 : ∀ i, pi i * (∑ j, inst.T k i j * (x' j - x j))
      ≤ (∑ j, |pi i| * |inst.T k i j|) * dist x x' := by
    intro i
    have step1 : |∑ j, inst.T k i j * (x' j - x j)| ≤ ∑ j, |inst.T k i j| * dist x x' := by
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
      refine Finset.sum_le_sum (fun j _ => ?_)
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hcoord j) (abs_nonneg _)
    calc pi i * (∑ j, inst.T k i j * (x' j - x j))
        ≤ |pi i * (∑ j, inst.T k i j * (x' j - x j))| := le_abs_self _
      _ = |pi i| * |∑ j, inst.T k i j * (x' j - x j)| := abs_mul _ _
      _ ≤ |pi i| * ∑ j, |inst.T k i j| * dist x x' :=
          mul_le_mul_of_nonneg_left step1 (abs_nonneg _)
      _ = (∑ j, |pi i| * |inst.T k i j|) * dist x x' := by
          rw [Finset.mul_sum, Finset.sum_mul]
          exact Finset.sum_congr rfl (fun j _ => by ring)
  have hsum : ∑ i, pi i * (∑ j, inst.T k i j * (x' j - x j)) ≤ F pi * dist x x' := by
    rw [hF]
    simp only
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum (fun i _ => hb1 i)
  have hFle : F pi ≤ max C0 0 := le_trans (hC0 ⟨pi, hpiV, rfl⟩) (le_max_left _ _)
  have hd : (0:ℝ) ≤ dist x x' := dist_nonneg
  calc (QVal inst x k).toReal - (QVal inst x' k).toReal
      ≤ dotProduct pi (inst.h k - Matrix.mulVec (inst.T k) x)
        - dotProduct pi (inst.h k - Matrix.mulVec (inst.T k) x') := by rw [hxr]; linarith
    _ = ∑ i, pi i * (∑ j, inst.T k i j * (x' j - x j)) := hval
    _ ≤ F pi * dist x x' := hsum
    _ ≤ max C0 0 * dist x x' := mul_le_mul_of_nonneg_right hFle hd

end StochasticProg.Recourse

namespace StochasticProg.Recourse

open scoped Classical

variable {n1 n2 m1 m2 K : ℕ}

lemma foldr_bookAdd_eq_coe_sum (N : ℕ) (a : Fin N → EReal) (r : Fin N → ℝ)
    (h : ∀ k, a k = ((r k : ℝ) : EReal)) :
    (List.ofFn a).foldr bookAdd 0 = ((∑ k, r k : ℝ) : EReal) :=
  le_antisymm (foldr_bookAdd_le_coe_sum N a r (fun k => le_of_eq (h k)))
    (coe_sum_le_foldr_bookAdd N a r (fun k => le_of_eq (h k).symm))

lemma Q_eq_coe_sum (inst : Instance n1 n2 m1 m2 K) (hQb : ∀ x k, QVal inst x k ≠ ⊥)
    {x : Fin n1 → ℝ} (hx : x ∈ K2 inst) :
    Q inst x = ((∑ k, (if 0 < inst.p k then inst.p k * (QVal inst x k).toReal else 0)
      : ℝ) : EReal) := by
  rw [Q_eq_foldr]
  refine foldr_bookAdd_eq_coe_sum K _ _ (fun k => ?_)
  by_cases hp : 0 < inst.p k
  · rw [if_pos hp]
    conv_lhs => rw [QVal_eq_coe inst hQb hx hp]
    rw [← EReal.coe_mul]
  · have hp0 : inst.p k = 0 := le_antisymm (not_lt.mp hp) (inst.hp_nonneg k)
    rw [if_neg hp, hp0]
    simp

lemma Q_toReal_eq (inst : Instance n1 n2 m1 m2 K) (hQb : ∀ x k, QVal inst x k ≠ ⊥)
    {x : Fin n1 → ℝ} (hx : x ∈ K2 inst) :
    (Q inst x).toReal
      = ∑ k, (if 0 < inst.p k then inst.p k * (QVal inst x k).toReal else 0) := by
  rw [Q_eq_coe_sum inst hQb hx]
  exact EReal.toReal_coe _

lemma convex_K2 (inst : Instance n1 n2 m1 m2 K) : Convex ℝ (K2 inst) := by
  intro x hx y hy a b ha hb hab
  have hmem : ∀ k, 0 < inst.p k → ∃ yy : Fin n2 → ℝ, (∀ l, 0 ≤ yy l) ∧
      Matrix.mulVec inst.W yy = inst.h k - Matrix.mulVec (inst.T k) (a • x + b • y) := by
    intro k hp
    obtain ⟨yx, hyx, hWx⟩ := feasible_of_K2 inst hx hp
    obtain ⟨yy, hyy, hWy⟩ := feasible_of_K2 inst hy hp
    refine ⟨a • yx + b • yy, fun l => ?_, ?_⟩
    · have h1 := mul_nonneg ha (hyx l)
      have h2 := mul_nonneg hb (hyy l)
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      linarith
    · rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hWx, hWy]
      funext i
      simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul,
        Matrix.mulVec_add, Matrix.mulVec_smul]
      linear_combination (inst.h k i) * hab
  show Q inst (a • x + b • y) ≠ ⊤
  rw [Q_ne_top_iff]
  intro k
  rw [scenario_term_ne_top_iff]
  intro hp
  exact hmem k hp

lemma convexOn_Q (inst : Instance n1 n2 m1 m2 K) (hQb : ∀ x k, QVal inst x k ≠ ⊥) :
    ConvexOn ℝ (K2 inst) (fun x => (Q inst x).toReal) := by
  refine ⟨convex_K2 inst, ?_⟩
  intro x hx y hy a b ha hb hab
  have hmem : a • x + b • y ∈ K2 inst := convex_K2 inst hx hy ha hb hab
  simp only [smul_eq_mul]
  rw [Q_toReal_eq inst hQb hmem, Q_toReal_eq inst hQb hx, Q_toReal_eq inst hQb hy,
    Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum (fun k _ => ?_)
  by_cases hp : 0 < inst.p k
  · rw [if_pos hp, if_pos hp, if_pos hp]
    obtain ⟨yx, hyx, hWx, hvx, _⟩ := scen_attained inst hQb hx hp
    obtain ⟨yy, hyy, hWy, hvy, _⟩ := scen_attained inst hQb hy hp
    have hfeas : Matrix.mulVec inst.W (a • yx + b • yy)
        = inst.h k - Matrix.mulVec (inst.T k) (a • x + b • y) := by
      rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hWx, hWy]
      funext i
      simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul,
        Matrix.mulVec_add, Matrix.mulVec_smul]
      linear_combination (inst.h k i) * hab
    have hnn : ∀ l, 0 ≤ (a • yx + b • yy) l := by
      intro l
      have h1 := mul_nonneg ha (hyx l)
      have h2 := mul_nonneg hb (hyy l)
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      linarith
    have hle : QVal inst (a • x + b • y) k
        ≤ ((dotProduct (inst.q k) (a • yx + b • yy) : ℝ) : EReal) :=
      sInf_le ⟨a • yx + b • yy, hnn, hfeas, rfl⟩
    rw [QVal_eq_coe inst hQb hmem hp] at hle
    have hle' : (QVal inst (a • x + b • y) k).toReal
        ≤ dotProduct (inst.q k) (a • yx + b • yy) := by exact_mod_cast hle
    have hexp : dotProduct (inst.q k) (a • yx + b • yy)
        = a * dotProduct (inst.q k) yx + b * dotProduct (inst.q k) yy := by
      simp only [dotProduct, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
        ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun l _ => by ring)
    have hvx' : (QVal inst x k).toReal = dotProduct (inst.q k) yx := by
      rw [hvx]; exact EReal.toReal_coe _
    have hvy' : (QVal inst y k).toReal = dotProduct (inst.q k) yy := by
      rw [hvy]; exact EReal.toReal_coe _
    rw [hexp] at hle'
    have hkey : (QVal inst (a • x + b • y) k).toReal
        ≤ a * (QVal inst x k).toReal + b * (QVal inst y k).toReal := by
      rw [hvx', hvy']; exact hle'
    have hstep := mul_le_mul_of_nonneg_left hkey (inst.hp_nonneg k)
    nlinarith [hstep]
  · rw [if_neg hp, if_neg hp, if_neg hp]
    simp

/-- Chapter 3, Theorem 6(a). -/
theorem thm6a_Q_lipschitz_convex_finite (inst : Instance n1 n2 m1 m2 K)
    (hQ : ∀ x k, QVal inst x k ≠ ⊥) :
    (∀ x ∈ K2 inst, ∃ r : ℝ, Q inst x = (r : EReal)) ∧
      ConvexOn ℝ (K2 inst) (fun x => (Q inst x).toReal) ∧
      ∃ L : NNReal, LipschitzOnWith L (fun x => (Q inst x).toReal) (K2 inst) := by
  classical
  refine ⟨?_, convexOn_Q inst hQ, ?_⟩
  · intro x hx
    exact ⟨(Q inst x).toReal, (EReal.coe_toReal hx (Q_ne_bot inst hQ x)).symm⟩
  · have hex : ∀ k, ∃ C : ℝ, 0 ≤ C ∧ (0 < inst.p k → ∀ x ∈ K2 inst, ∀ x' ∈ K2 inst,
        (QVal inst x k).toReal - (QVal inst x' k).toReal ≤ C * dist x x') := by
      intro k
      by_cases hp : 0 < inst.p k
      · obtain ⟨C, hC0, hC⟩ := scen_lipschitz inst hQ k hp
        exact ⟨C, hC0, fun _ => hC⟩
      · exact ⟨0, le_rfl, fun h => absurd h hp⟩
    choose C hC0 hC using hex
    have hL0 : 0 ≤ ∑ k, inst.p k * C k :=
      Finset.sum_nonneg (fun k _ => mul_nonneg (inst.hp_nonneg k) (hC0 k))
    refine ⟨⟨∑ k, inst.p k * C k, hL0⟩, ?_⟩
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx x' hx'
    have hone : ∀ u ∈ K2 inst, ∀ u' ∈ K2 inst,
        (Q inst u).toReal - (Q inst u').toReal ≤ (∑ k, inst.p k * C k) * dist u u' := by
      intro u hu u' hu'
      rw [Q_toReal_eq inst hQ hu, Q_toReal_eq inst hQ hu', ← Finset.sum_sub_distrib,
        Finset.sum_mul]
      refine Finset.sum_le_sum (fun k _ => ?_)
      by_cases hp : 0 < inst.p k
      · rw [if_pos hp, if_pos hp]
        have h := hC k hp u hu u' hu'
        have hstep := mul_le_mul_of_nonneg_left h (inst.hp_nonneg k)
        nlinarith [hstep]
      · have hp0 : inst.p k = 0 := le_antisymm (not_lt.mp hp) (inst.hp_nonneg k)
        rw [if_neg hp, if_neg hp, hp0]
        simp
    rw [Real.dist_eq, abs_sub_le_iff]
    have hd1 := hone x hx x' hx'
    have hd2 := hone x' hx' x hx
    rw [dist_comm x' x] at hd2
    refine ⟨?_, ?_⟩
    · show (Q inst x).toReal - (Q inst x').toReal ≤ (∑ k, inst.p k * C k) * dist x x'
      exact hd1
    · show (Q inst x').toReal - (Q inst x).toReal ≤ (∑ k, inst.p k * C k) * dist x x'
      exact hd2


/-- Top-level entry point: Birge & Louveaux, Chapter 3, Theorem 6(a). -/
theorem _root_.solution (inst : Instance n1 n2 m1 m2 K)
    (hQ : ∀ x k, QVal inst x k ≠ ⊥) :
    (∀ x ∈ K2 inst, ∃ r : ℝ, Q inst x = (r : EReal)) ∧
      ConvexOn ℝ (K2 inst) (fun x => (Q inst x).toReal) ∧
      ∃ L : NNReal, LipschitzOnWith L (fun x => (Q inst x).toReal) (K2 inst) :=
  thm6a_Q_lipschitz_convex_finite inst hQ

end StochasticProg.Recourse
