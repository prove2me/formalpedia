-- Prove2me | solution 1 for StochasticProg.Recourse.thm9_kkt_optimality
-- status  : ACCEPTED   (prove)
-- author  : @Hartmann_Psi
-- created : 2026-09-27T23:45:47.082976+00:00
-- url     : https://prove2.me/submissions/04a7004d-8b1b-424c-89fb-972a9ebf5801

import Mathlib
import Definitions.Def_StochasticProg_Recourse_Instance
import Definitions.Def_StochasticProg_Recourse_Subdiff


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

namespace LPAttain

open Matrix

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
      ConeGen.coneSpan (augCol W q) := by
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
    exact (ConeGen.isClosed_coneSpan _).preimage hcont
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

end LPAttain

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

/-- Scenario recourse matrix, neutralised on scenarios of probability zero. -/
noncomputable def scenW (inst : Instance n1 n2 m1 m2 K) (k : Fin K) :
    Matrix (Fin m2) (Fin n2) ℝ := if 0 < inst.p k then inst.W else 0

/-- Scenario technology matrix, neutralised on scenarios of probability zero. -/
noncomputable def scenT (inst : Instance n1 n2 m1 m2 K) (k : Fin K) :
    Matrix (Fin m2) (Fin n1) ℝ := if 0 < inst.p k then inst.T k else 0

/-- Scenario right-hand side, neutralised on scenarios of probability zero. -/
noncomputable def scenH (inst : Instance n1 n2 m1 m2 K) (k : Fin K) :
    Fin m2 → ℝ := if 0 < inst.p k then inst.h k else 0

/-- The constraint matrix of the deterministic equivalent, written as a single matrix over
the sum/product index types. -/
noncomputable def bigM (inst : Instance n1 n2 m1 m2 K) :
    Matrix (Fin m1 ⊕ Fin K × Fin m2) (Fin n1 ⊕ Fin K × Fin n2) ℝ :=
  Matrix.of fun I J =>
    Sum.elim
      (fun i : Fin m1 => Sum.elim (fun j : Fin n1 => inst.A i j) (fun _ => (0:ℝ)) J)
      (fun ki : Fin K × Fin m2 =>
        Sum.elim (fun j : Fin n1 => scenT inst ki.1 ki.2 j)
          (fun kl : Fin K × Fin n2 =>
            if ki.1 = kl.1 then scenW inst ki.1 ki.2 kl.2 else (0:ℝ)) J) I

/-- Right-hand side of the deterministic equivalent. -/
noncomputable def bigG (inst : Instance n1 n2 m1 m2 K) : Fin m1 ⊕ Fin K × Fin m2 → ℝ :=
  Sum.elim inst.b (fun ki => scenH inst ki.1 ki.2)

/-- Cost vector of the deterministic equivalent. -/
noncomputable def bigD (inst : Instance n1 n2 m1 m2 K) : Fin n1 ⊕ Fin K × Fin n2 → ℝ :=
  Sum.elim inst.c (fun kl => inst.p kl.1 * inst.q kl.1 kl.2)

@[simp] lemma bigM_inl_inl (inst : Instance n1 n2 m1 m2 K) (i : Fin m1) (j : Fin n1) :
    bigM inst (Sum.inl i) (Sum.inl j) = inst.A i j := rfl

@[simp] lemma bigM_inl_inr (inst : Instance n1 n2 m1 m2 K) (i : Fin m1) (kl : Fin K × Fin n2) :
    bigM inst (Sum.inl i) (Sum.inr kl) = 0 := rfl

@[simp] lemma bigM_inr_inl (inst : Instance n1 n2 m1 m2 K) (ki : Fin K × Fin m2) (j : Fin n1) :
    bigM inst (Sum.inr ki) (Sum.inl j) = scenT inst ki.1 ki.2 j := rfl

@[simp] lemma bigM_inr_inr (inst : Instance n1 n2 m1 m2 K) (ki : Fin K × Fin m2)
    (kl : Fin K × Fin n2) :
    bigM inst (Sum.inr ki) (Sum.inr kl) =
      if ki.1 = kl.1 then scenW inst ki.1 ki.2 kl.2 else 0 := rfl

lemma bigM_mulVec_inl (inst : Instance n1 n2 m1 m2 K)
    (u : Fin n1 ⊕ Fin K × Fin n2 → ℝ) (i : Fin m1) :
    Matrix.mulVec (bigM inst) u (Sum.inl i)
      = Matrix.mulVec inst.A (fun j => u (Sum.inl j)) i := by
  simp only [Matrix.mulVec, dotProduct]
  rw [Fintype.sum_sum_type]
  simp

lemma bigM_mulVec_inr (inst : Instance n1 n2 m1 m2 K)
    (u : Fin n1 ⊕ Fin K × Fin n2 → ℝ) (k : Fin K) (i : Fin m2) :
    Matrix.mulVec (bigM inst) u (Sum.inr (k, i))
      = Matrix.mulVec (scenT inst k) (fun j => u (Sum.inl j)) i
        + Matrix.mulVec (scenW inst k) (fun l => u (Sum.inr (k, l))) i := by
  classical
  have h1 : ∑ j : Fin n1, bigM inst (Sum.inr (k, i)) (Sum.inl j) * u (Sum.inl j)
      = Matrix.mulVec (scenT inst k) (fun j => u (Sum.inl j)) i := rfl
  have h2 : ∑ kl : Fin K × Fin n2, bigM inst (Sum.inr (k, i)) (Sum.inr kl) * u (Sum.inr kl)
      = Matrix.mulVec (scenW inst k) (fun l => u (Sum.inr (k, l))) i := by
    simp only [bigM_inr_inr, Matrix.mulVec, dotProduct]
    rw [Fintype.sum_prod_type, Finset.sum_eq_single k]
    · simp
    · intro b _ hb; simp [Ne.symm hb]
    · simp
  have hsplit : Matrix.mulVec (bigM inst) u (Sum.inr (k, i))
      = (∑ j : Fin n1, bigM inst (Sum.inr (k, i)) (Sum.inl j) * u (Sum.inl j))
        + (∑ kl : Fin K × Fin n2, bigM inst (Sum.inr (k, i)) (Sum.inr kl) * u (Sum.inr kl)) := by
    simp only [Matrix.mulVec, dotProduct]
    rw [Fintype.sum_sum_type]
  rw [hsplit, h1, h2]

lemma bigM_vecMul_inr (inst : Instance n1 n2 m1 m2 K)
    (pv : Fin m1 ⊕ Fin K × Fin m2 → ℝ) (k : Fin K) (l : Fin n2) :
    Matrix.mulVec (Matrix.transpose (bigM inst)) pv (Sum.inr (k, l))
      = Matrix.mulVec (Matrix.transpose (scenW inst k)) (fun i => pv (Sum.inr (k, i))) l := by
  classical
  have h1 : ∑ i : Fin m1, bigM inst (Sum.inl i) (Sum.inr (k, l)) * pv (Sum.inl i) = 0 := by
    simp
  have h2 : ∑ ki : Fin K × Fin m2, bigM inst (Sum.inr ki) (Sum.inr (k, l)) * pv (Sum.inr ki)
      = Matrix.mulVec (Matrix.transpose (scenW inst k)) (fun i => pv (Sum.inr (k, i))) l := by
    simp only [bigM_inr_inr, Matrix.mulVec, dotProduct, Matrix.transpose_apply]
    rw [Fintype.sum_prod_type, Finset.sum_eq_single k]
    · simp
    · intro b _ hb; simp [hb]
    · simp
  have hsplit : Matrix.mulVec (Matrix.transpose (bigM inst)) pv (Sum.inr (k, l))
      = (∑ i : Fin m1, bigM inst (Sum.inl i) (Sum.inr (k, l)) * pv (Sum.inl i))
        + (∑ ki : Fin K × Fin m2, bigM inst (Sum.inr ki) (Sum.inr (k, l)) * pv (Sum.inr ki)) := by
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply]
    rw [Fintype.sum_sum_type]
  rw [hsplit, h1, h2, zero_add]

lemma bigM_vecMul_inl (inst : Instance n1 n2 m1 m2 K)
    (pv : Fin m1 ⊕ Fin K × Fin m2 → ℝ) (j : Fin n1) :
    Matrix.mulVec (Matrix.transpose (bigM inst)) pv (Sum.inl j)
      = Matrix.mulVec (Matrix.transpose inst.A) (fun i => pv (Sum.inl i)) j
        + ∑ k, Matrix.mulVec (Matrix.transpose (scenT inst k))
            (fun i => pv (Sum.inr (k, i))) j := by
  have h1 : ∑ i : Fin m1, bigM inst (Sum.inl i) (Sum.inl j) * pv (Sum.inl i)
      = Matrix.mulVec (Matrix.transpose inst.A) (fun i => pv (Sum.inl i)) j := rfl
  have h2 : ∑ ki : Fin K × Fin m2, bigM inst (Sum.inr ki) (Sum.inl j) * pv (Sum.inr ki)
      = ∑ k, Matrix.mulVec (Matrix.transpose (scenT inst k))
          (fun i => pv (Sum.inr (k, i))) j := by
    simp only [bigM_inr_inl, Matrix.mulVec, dotProduct, Matrix.transpose_apply]
    rw [Fintype.sum_prod_type]
  have hsplit : Matrix.mulVec (Matrix.transpose (bigM inst)) pv (Sum.inl j)
      = (∑ i : Fin m1, bigM inst (Sum.inl i) (Sum.inl j) * pv (Sum.inl i))
        + (∑ ki : Fin K × Fin m2, bigM inst (Sum.inr ki) (Sum.inl j) * pv (Sum.inr ki)) := by
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply]
    rw [Fintype.sum_sum_type]
  rw [hsplit, h1, h2]

lemma bigD_dot (inst : Instance n1 n2 m1 m2 K) (u : Fin n1 ⊕ Fin K × Fin n2 → ℝ) :
    dotProduct (bigD inst) u
      = dotProduct inst.c (fun j => u (Sum.inl j))
        + ∑ k, inst.p k * dotProduct (inst.q k) (fun l => u (Sum.inr (k, l))) := by
  simp only [dotProduct, bigD]
  rw [Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr]
  congr 1
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun l _ => by ring)

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

/-- Weak duality, scenario by scenario, with the neutralised data. -/
lemma scenario_weak_duality (inst : Instance n1 n2 m1 m2 K)
    (pik : Fin K → Fin m2 → ℝ)
    (hdf : ∀ k l, Matrix.mulVec (Matrix.transpose (scenW inst k)) (pik k) l
      ≤ inst.p k * inst.q k l)
    (y : Fin n1 → ℝ) (k : Fin K) :
    ((dotProduct (pik k) (scenH inst k - Matrix.mulVec (scenT inst k) y) : ℝ) : EReal)
      ≤ ((inst.p k : ℝ) : EReal) * QVal inst y k := by
  by_cases hp : 0 < inst.p k
  · set c0 : ℝ := dotProduct (pik k) (scenH inst k - Matrix.mulVec (scenT inst k) y) with hc0
    have hW : scenW inst k = inst.W := by simp [scenW, hp]
    have hT : scenT inst k = inst.T k := by simp [scenT, hp]
    have hH : scenH inst k = inst.h k := by simp [scenH, hp]
    have hbound : ((c0 / inst.p k : ℝ) : EReal) ≤ QVal inst y k := by
      rw [QVal]
      refine le_sInf ?_
      rintro z ⟨yy, hyy, hWyy, rfl⟩
      have h1 : c0 ≤ dotProduct (fun l => inst.p k * inst.q k l) yy := by
        have h2 : dotProduct (Matrix.mulVec (Matrix.transpose (scenW inst k)) (pik k)) yy
            ≤ dotProduct (fun l => inst.p k * inst.q k l) yy :=
          Finset.sum_le_sum (fun l _ => mul_le_mul_of_nonneg_right (hdf k l) (hyy l))
        have h3 : dotProduct (Matrix.mulVec (Matrix.transpose (scenW inst k)) (pik k)) yy
            = dotProduct (pik k) (Matrix.mulVec (scenW inst k) yy) := by
          rw [Matrix.dotProduct_mulVec, Matrix.mulVec_transpose]
        rw [h3, hW, hWyy] at h2
        rw [hc0, hT, hH]
        exact h2
      have h4 : c0 / inst.p k ≤ dotProduct (inst.q k) yy := by
        rw [div_le_iff₀ hp]
        have : dotProduct (fun l => inst.p k * inst.q k l) yy
            = dotProduct (inst.q k) yy * inst.p k := by
          simp only [dotProduct]
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl (fun l _ => by ring)
        rw [← this]; exact h1
      exact_mod_cast h4
    have hmul := mul_le_mul_of_nonneg_left hbound
      (le_of_lt (by exact_mod_cast hp : (0 : EReal) < ((inst.p k : ℝ) : EReal)))
    refine le_trans ?_ hmul
    rw [← EReal.coe_mul]
    apply le_of_eq
    congr 1
    field_simp
  · have hp0 : inst.p k = 0 := le_antisymm (not_lt.mp hp) (inst.hp_nonneg k)
    have hT : scenT inst k = 0 := by simp [scenT, hp]
    have hH : scenH inst k = 0 := by simp [scenH, hp]
    rw [hT, hH]
    simp [hp0, dotProduct]

end StochasticProg.Recourse

namespace StochasticProg.Recourse

open scoped Classical

variable {n1 n2 m1 m2 K : ℕ}

lemma foldr_bookAdd_eq_coe_sum (N : ℕ) (a : Fin N → EReal) (r : Fin N → ℝ)
    (h : ∀ k, a k = ((r k : ℝ) : EReal)) :
    (List.ofFn a).foldr bookAdd 0 = ((∑ k, r k : ℝ) : EReal) :=
  le_antisymm (foldr_bookAdd_le_coe_sum N a r (fun k => le_of_eq (h k)))
    (coe_sum_le_foldr_bookAdd N a r (fun k => le_of_eq (h k).symm))

/-- Chapter 3, Theorem 9. -/
theorem thm9_kkt_optimality (inst : Instance n1 n2 m1 m2 K)
    (hQb : ∀ x k, QVal inst x k ≠ ⊥)
    (hfin : ∃ z0 : ℝ, sInf (obj inst '' K1 inst) = (z0 : EReal))
    (xstar : Fin n1 → ℝ) (hx : xstar ∈ K1 inst) :
    (obj inst xstar = sInf (obj inst '' K1 inst)) ↔
      ∃ (lam : Fin m1 → ℝ) (mu : Fin n1 → ℝ),
        (∀ i, 0 ≤ mu i) ∧ dotProduct mu xstar = 0 ∧
        (fun j => -inst.c j + Matrix.mulVec (Matrix.transpose inst.A) lam j + mu j) ∈
          subdiffQ inst xstar := by
  classical
  have hAxs : Matrix.mulVec inst.A xstar = inst.b := hx.1
  have hxsnn : ∀ j, 0 ≤ xstar j := hx.2
  constructor
  · -- hard direction
    intro hoptstar
    obtain ⟨z0, hz0⟩ := hfin
    have hobjstar : obj inst xstar = ((z0 : ℝ) : EReal) := by rw [hoptstar, hz0]
    have hQtop : Q inst xstar ≠ ⊤ := by
      intro h
      rw [obj, h] at hobjstar
      simp at hobjstar
    have hQbot : Q inst xstar ≠ ⊥ := Q_ne_bot inst hQb xstar
    -- scenario objectives
    set qq : Fin K → Fin n2 → ℝ := fun k l => inst.p k * inst.q k l with hqq
    -- per-scenario feasibility and boundedness
    have hQterm : ∀ k, ((inst.p k : ℝ) : EReal) * QVal inst xstar k ≠ ⊤ :=
      (Q_ne_top_iff inst xstar).mp hQtop
    have hscen : ∀ k, ∃ y : Fin n2 → ℝ, (∀ l, 0 ≤ y l) ∧
        Matrix.mulVec (scenW inst k) y = (scenH inst k - Matrix.mulVec (scenT inst k) xstar) ∧
        ∀ y' : Fin n2 → ℝ, (∀ l, 0 ≤ y' l) → Matrix.mulVec (scenW inst k) y' = (scenH inst k - Matrix.mulVec (scenT inst k) xstar) →
          dotProduct (qq k) y ≤ dotProduct (qq k) y' := by
      intro k
      by_cases hp : 0 < inst.p k
      · have hW : scenW inst k = inst.W := by simp [scenW, hp]
        have hT : scenT inst k = inst.T k := by simp [scenT, hp]
        have hH : scenH inst k = inst.h k := by simp [scenH, hp]
        have hVtop : QVal inst xstar k ≠ ⊤ :=
          (QVal_ne_top_iff inst xstar k).mpr
            ((scenario_term_ne_top_iff inst xstar k).mp (hQterm k) hp)
        have hfeas : ∃ y : Fin n2 → ℝ, (∀ l, 0 ≤ y l) ∧
            Matrix.mulVec (scenW inst k) y = (scenH inst k - Matrix.mulVec (scenT inst k) xstar) := by
          obtain ⟨y, hy, hWy⟩ := (QVal_ne_top_iff inst xstar k).mp hVtop
          exact ⟨y, hy, by rw [hW, hT, hH]; exact hWy⟩
        have hVbot : QVal inst xstar k ≠ ⊥ := hQb xstar k
        set rk : ℝ := (QVal inst xstar k).toReal with hrk
        have hVeq : QVal inst xstar k = ((rk : ℝ) : EReal) := (EReal.coe_toReal hVtop hVbot).symm
        have hbdd : ∃ beta : ℝ, ∀ y : Fin n2 → ℝ, (∀ l, 0 ≤ y l) →
            Matrix.mulVec (scenW inst k) y = (scenH inst k - Matrix.mulVec (scenT inst k) xstar) → beta ≤ dotProduct (qq k) y := by
          refine ⟨inst.p k * rk, ?_⟩
          intro y hy hWy
          have hmem : ((dotProduct (inst.q k) y : ℝ) : EReal) ∈
              {z : EReal | ∃ yy : Fin n2 → ℝ, (∀ i, 0 ≤ yy i) ∧
                Matrix.mulVec inst.W yy = inst.h k - Matrix.mulVec (inst.T k) xstar ∧
                z = ((dotProduct (inst.q k) yy : ℝ) : EReal)} := by
            refine ⟨y, hy, ?_, rfl⟩
            rw [← hW, hWy, hT, hH]
          have hle : QVal inst xstar k ≤ ((dotProduct (inst.q k) y : ℝ) : EReal) := sInf_le hmem
          rw [hVeq] at hle
          have hle' : rk ≤ dotProduct (inst.q k) y := by exact_mod_cast hle
          have : dotProduct (qq k) y = inst.p k * dotProduct (inst.q k) y := by
            simp only [dotProduct, hqq, Finset.mul_sum]
            exact Finset.sum_congr rfl (fun l _ => by ring)
          rw [this]
          exact mul_le_mul_of_nonneg_left hle' hp.le
        exact LPAttain.lp_min_attained _ _ _ hfeas hbdd
      · have hp0 : inst.p k = 0 := le_antisymm (not_lt.mp hp) (inst.hp_nonneg k)
        have hW : scenW inst k = 0 := by simp [scenW, hp]
        have hT : scenT inst k = 0 := by simp [scenT, hp]
        have hH : scenH inst k = 0 := by simp [scenH, hp]
        refine ⟨0, fun _ => le_rfl, ?_, ?_⟩
        · rw [hW, hT, hH]; simp
        · intro y' _ _
          simp [hqq, hp0, dotProduct]
    choose ystar hystar_nn hystar_feas hystar_min using hscen
    have hQval : ∀ k, ((inst.p k : ℝ) : EReal) * QVal inst xstar k
        = ((dotProduct (qq k) (ystar k) : ℝ) : EReal) := by
      intro k
      have hscale : ∀ z : Fin n2 → ℝ,
          dotProduct (qq k) z = inst.p k * dotProduct (inst.q k) z := by
        intro z
        simp only [hqq, dotProduct, Finset.mul_sum]
        exact Finset.sum_congr rfl (fun l _ => by ring)
      by_cases hp : 0 < inst.p k
      · have hW : scenW inst k = inst.W := by simp [scenW, hp]
        have hT : scenT inst k = inst.T k := by simp [scenT, hp]
        have hH : scenH inst k = inst.h k := by simp [scenH, hp]
        have hfeasstar : Matrix.mulVec inst.W (ystar k)
            = inst.h k - Matrix.mulVec (inst.T k) xstar := by
          have h := hystar_feas k; rw [hW, hT, hH] at h; exact h
        have hmem : ((dotProduct (inst.q k) (ystar k) : ℝ) : EReal) ∈
            {z : EReal | ∃ yy : Fin n2 → ℝ, (∀ i, 0 ≤ yy i) ∧
              Matrix.mulVec inst.W yy = inst.h k - Matrix.mulVec (inst.T k) xstar ∧
              z = ((dotProduct (inst.q k) yy : ℝ) : EReal)} :=
          ⟨ystar k, hystar_nn k, hfeasstar, rfl⟩
        have h1 : QVal inst xstar k ≤ ((dotProduct (inst.q k) (ystar k) : ℝ) : EReal) :=
          sInf_le hmem
        have h2 : ((dotProduct (inst.q k) (ystar k) : ℝ) : EReal) ≤ QVal inst xstar k := by
          rw [QVal]
          refine le_sInf ?_
          rintro z ⟨yy, hyy, hWyy, rfl⟩
          have hfeasyy : Matrix.mulVec (scenW inst k) yy
              = scenH inst k - Matrix.mulVec (scenT inst k) xstar := by
            rw [hW, hT, hH]; exact hWyy
          have hmin := hystar_min k yy hyy hfeasyy
          rw [hscale, hscale] at hmin
          have hle := le_of_mul_le_mul_left hmin hp
          exact_mod_cast hle
        have hEq : QVal inst xstar k = ((dotProduct (inst.q k) (ystar k) : ℝ) : EReal) :=
          le_antisymm h1 h2
        rw [hEq, ← EReal.coe_mul, hscale]
      · have hp0 : inst.p k = 0 := le_antisymm (not_lt.mp hp) (inst.hp_nonneg k)
        rw [hscale, hp0]
        simp
    have hQstar_eq : Q inst xstar
        = ((∑ k, dotProduct (qq k) (ystar k) : ℝ) : EReal) := by
      rw [Q_eq_foldr]
      exact foldr_bookAdd_eq_coe_sum K _ _ hQval
    set u0 : Fin n1 ⊕ Fin K × Fin n2 → ℝ :=
      Sum.elim xstar (fun kl => ystar kl.1 kl.2) with hu0def
    have hux : (fun j => u0 (Sum.inl j)) = xstar := rfl
    have huy : ∀ k, (fun l => u0 (Sum.inr (k, l))) = ystar k := fun k => rfl
    have hu0nn : ∀ J, 0 ≤ u0 J := by
      rintro (j | ⟨k, l⟩)
      · exact hxsnn j
      · exact hystar_nn k l
    have hu0feas : Matrix.mulVec (bigM inst) u0 = bigG inst := by
      funext I
      rcases I with i | ⟨k, i⟩
      · rw [bigM_mulVec_inl, hux, hAxs]; rfl
      · rw [bigM_mulVec_inr, hux, huy k, hystar_feas k]
        simp only [bigG, Sum.elim_inr, Pi.sub_apply]
        ring
    have hu0opt : ∀ u : Fin n1 ⊕ Fin K × Fin n2 → ℝ, (∀ J, 0 ≤ u J) →
        Matrix.mulVec (bigM inst) u = bigG inst →
        dotProduct (bigD inst) u0 ≤ dotProduct (bigD inst) u := by
      intro u hunn hufeas
      have hAxx : Matrix.mulVec inst.A (fun j => u (Sum.inl j)) = inst.b := by
        funext i
        have h := congrArg (fun f => f (Sum.inl i)) hufeas
        rw [bigM_mulVec_inl] at h
        exact h
      have hxxK1 : (fun j => u (Sum.inl j)) ∈ K1 inst := ⟨hAxx, fun j => hunn _⟩
      have hWyy : ∀ k, Matrix.mulVec (scenW inst k) (fun l => u (Sum.inr (k, l)))
          = scenH inst k - Matrix.mulVec (scenT inst k) (fun j => u (Sum.inl j)) := by
        intro k
        funext i
        have h := congrArg (fun f => f (Sum.inr (k, i))) hufeas
        rw [bigM_mulVec_inr] at h
        simp only [bigG, Sum.elim_inr] at h
        simp only [Pi.sub_apply]
        linarith
      have hscale : ∀ (k : Fin K) (z : Fin n2 → ℝ),
          dotProduct (qq k) z = inst.p k * dotProduct (inst.q k) z := by
        intro k z
        simp only [hqq, dotProduct, Finset.mul_sum]
        exact Finset.sum_congr rfl (fun l _ => by ring)
      have hterm : ∀ k, ((inst.p k : ℝ) : EReal) * QVal inst (fun j => u (Sum.inl j)) k
          ≤ ((dotProduct (qq k) (fun l => u (Sum.inr (k, l))) : ℝ) : EReal) := by
        intro k
        by_cases hp : 0 < inst.p k
        · have hW : scenW inst k = inst.W := by simp [scenW, hp]
          have hT : scenT inst k = inst.T k := by simp [scenT, hp]
          have hH : scenH inst k = inst.h k := by simp [scenH, hp]
          have hfy : Matrix.mulVec inst.W (fun l => u (Sum.inr (k, l)))
              = inst.h k - Matrix.mulVec (inst.T k) (fun j => u (Sum.inl j)) := by
            have h := hWyy k; rw [hW, hT, hH] at h; exact h
          have hmem : ((dotProduct (inst.q k) (fun l => u (Sum.inr (k, l))) : ℝ) : EReal) ∈
              {z : EReal | ∃ yy : Fin n2 → ℝ, (∀ i, 0 ≤ yy i) ∧
                Matrix.mulVec inst.W yy
                  = inst.h k - Matrix.mulVec (inst.T k) (fun j => u (Sum.inl j)) ∧
                z = ((dotProduct (inst.q k) yy : ℝ) : EReal)} :=
            ⟨_, fun l => hunn _, hfy, rfl⟩
          have h1 : QVal inst (fun j => u (Sum.inl j)) k
              ≤ ((dotProduct (inst.q k) (fun l => u (Sum.inr (k, l))) : ℝ) : EReal) :=
            sInf_le hmem
          have hmul := mul_le_mul_of_nonneg_left h1
            (by exact_mod_cast inst.hp_nonneg k : (0 : EReal) ≤ ((inst.p k : ℝ) : EReal))
          refine le_trans hmul (le_of_eq ?_)
          rw [← EReal.coe_mul, hscale]
        · have hp0 : inst.p k = 0 := le_antisymm (not_lt.mp hp) (inst.hp_nonneg k)
          rw [hscale, hp0]
          simp
      have hQxx : Q inst (fun j => u (Sum.inl j))
          ≤ ((∑ k, dotProduct (qq k) (fun l => u (Sum.inr (k, l))) : ℝ) : EReal) := by
        rw [Q_eq_foldr]
        exact foldr_bookAdd_le_coe_sum K _ _ hterm
      have hbigD : ∀ w : Fin n1 ⊕ Fin K × Fin n2 → ℝ, dotProduct (bigD inst) w
          = dotProduct inst.c (fun j => w (Sum.inl j))
            + ∑ k, dotProduct (qq k) (fun l => w (Sum.inr (k, l))) := by
        intro w
        rw [bigD_dot]
        congr 1
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [hscale]
      have hobjle : obj inst (fun j => u (Sum.inl j))
          ≤ ((dotProduct (bigD inst) u : ℝ) : EReal) := by
        rw [hbigD u, EReal.coe_add]
        exact add_le_add (le_refl _) hQxx
      have hstarle : obj inst xstar ≤ obj inst (fun j => u (Sum.inl j)) := by
        rw [hoptstar]
        exact sInf_le (Set.mem_image_of_mem _ hxxK1)
      have hu0val : ((dotProduct (bigD inst) u0 : ℝ) : EReal) = obj inst xstar := by
        rw [hbigD u0]
        simp only [hux, huy]
        rw [EReal.coe_add]
        simp only [obj]
        rw [hQstar_eq]
      have hfinal : ((dotProduct (bigD inst) u0 : ℝ) : EReal)
          ≤ ((dotProduct (bigD inst) u : ℝ) : EReal) := by
        rw [hu0val]
        exact le_trans hstarle hobjle
      exact_mod_cast hfinal
    obtain ⟨pv, hdf, hvaleq, hcs⟩ :=
      LPGen.lp_strong_duality (bigM inst) (bigD inst) (bigG inst) u0 hu0nn hu0feas hu0opt
    have hdfk : ∀ k l, Matrix.mulVec (Matrix.transpose (scenW inst k))
        (fun i => pv (Sum.inr (k, i))) l ≤ inst.p k * inst.q k l := by
      intro k l
      have h := hdf (Sum.inr (k, l))
      rw [bigM_vecMul_inr] at h
      simpa [bigD] using h
    have hcfk : ∀ k, dotProduct (fun i => pv (Sum.inr (k, i)))
        (scenH inst k - Matrix.mulVec (scenT inst k) xstar)
        = dotProduct (qq k) (ystar k) := by
      intro k
      have hzero : ∀ l, ystar k l * (inst.p k * inst.q k l
          - Matrix.mulVec (Matrix.transpose (scenW inst k))
              (fun i => pv (Sum.inr (k, i))) l) = 0 := by
        intro l
        have h := hcs (Sum.inr (k, l))
        rw [bigM_vecMul_inr] at h
        have hbd : bigD inst (Sum.inr (k, l)) = inst.p k * inst.q k l := rfl
        rw [hbd] at h
        exact h
      have hsum : dotProduct (qq k) (ystar k)
          = dotProduct (Matrix.mulVec (Matrix.transpose (scenW inst k))
              (fun i => pv (Sum.inr (k, i)))) (ystar k) := by
        simp only [dotProduct, hqq]
        refine Finset.sum_congr rfl (fun l _ => ?_)
        linear_combination hzero l
      rw [hsum, Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec, hystar_feas k]
    have hC : ∀ y : Fin n1 → ℝ,
        ∑ k, dotProduct (fun i => pv (Sum.inr (k, i)))
            (scenH inst k - Matrix.mulVec (scenT inst k) y)
          = (∑ k, dotProduct (fun i => pv (Sum.inr (k, i))) (scenH inst k))
            + dotProduct (fun j => -∑ k, Matrix.mulVec (Matrix.transpose (scenT inst k))
                (fun i => pv (Sum.inr (k, i))) j) y := by
      intro y
      have hstep : ∀ k, dotProduct (fun i => pv (Sum.inr (k, i)))
          (scenH inst k - Matrix.mulVec (scenT inst k) y)
          = dotProduct (fun i => pv (Sum.inr (k, i))) (scenH inst k)
            - dotProduct (Matrix.mulVec (Matrix.transpose (scenT inst k))
                (fun i => pv (Sum.inr (k, i)))) y := by
        intro k
        rw [Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec]
        simp only [dotProduct, Pi.sub_apply]
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl (fun i _ => by ring)
      have h2 : dotProduct (fun j => -∑ k, Matrix.mulVec (Matrix.transpose (scenT inst k))
            (fun i => pv (Sum.inr (k, i))) j) y
          = -∑ k, dotProduct (Matrix.mulVec (Matrix.transpose (scenT inst k))
            (fun i => pv (Sum.inr (k, i)))) y := by
        simp only [dotProduct]
        have e1 : ∀ j : Fin n1, (-∑ k, Matrix.mulVec (Matrix.transpose (scenT inst k))
              (fun i => pv (Sum.inr (k, i))) j) * y j
            = -∑ k, Matrix.mulVec (Matrix.transpose (scenT inst k))
                (fun i => pv (Sum.inr (k, i))) j * y j := by
          intro j; rw [neg_mul, Finset.sum_mul]
        rw [Finset.sum_congr rfl (fun j _ => e1 j), Finset.sum_neg_distrib]
        congr 1
        exact Finset.sum_comm
      rw [h2]
      simp only [hstep]
      rw [Finset.sum_sub_distrib]
      ring
    have hpsi_le : ∀ y : Fin n1 → ℝ,
        ((∑ k, dotProduct (fun i => pv (Sum.inr (k, i)))
            (scenH inst k - Matrix.mulVec (scenT inst k) y) : ℝ) : EReal) ≤ Q inst y := by
      intro y
      rw [Q_eq_foldr]
      exact coe_sum_le_foldr_bookAdd K _ _
        (fun k => scenario_weak_duality inst (fun k i => pv (Sum.inr (k, i))) hdfk y k)
    refine ⟨fun i => pv (Sum.inl i),
      fun j => inst.c j - Matrix.mulVec (Matrix.transpose inst.A) (fun i => pv (Sum.inl i)) j
        - ∑ k, Matrix.mulVec (Matrix.transpose (scenT inst k))
            (fun i => pv (Sum.inr (k, i))) j, ?_, ?_, ?_⟩
    · intro j
      have h := hdf (Sum.inl j)
      rw [bigM_vecMul_inl] at h
      simp only [bigD, Sum.elim_inl] at h
      simp only
      linarith
    · simp only [dotProduct]
      refine Finset.sum_eq_zero (fun j _ => ?_)
      have h := hcs (Sum.inl j)
      rw [bigM_vecMul_inl] at h
      simp only [bigD, Sum.elim_inl] at h
      have hx0 : u0 (Sum.inl j) = xstar j := rfl
      rw [hx0] at h
      linear_combination h
    · intro y
      have hQxstar : Q inst xstar = ((∑ k, dotProduct (fun i => pv (Sum.inr (k, i)))
          (scenH inst k - Matrix.mulVec (scenT inst k) xstar) : ℝ) : EReal) := by
        rw [hQstar_eq]
        congr 1
        exact Finset.sum_congr rfl (fun k _ => (hcfk k).symm)
      rw [hQxstar, ← EReal.coe_add]
      refine le_trans (le_of_eq ?_) (hpsi_le y)
      congr 1
      rw [hC xstar, hC y]
      have hlin : dotProduct (fun j => -inst.c j
            + Matrix.mulVec (Matrix.transpose inst.A) (fun i => pv (Sum.inl i)) j
            + (inst.c j - Matrix.mulVec (Matrix.transpose inst.A) (fun i => pv (Sum.inl i)) j
              - ∑ k, Matrix.mulVec (Matrix.transpose (scenT inst k))
                  (fun i => pv (Sum.inr (k, i))) j)) (y - xstar)
          = dotProduct (fun j => -∑ k, Matrix.mulVec (Matrix.transpose (scenT inst k))
              (fun i => pv (Sum.inr (k, i))) j) y
            - dotProduct (fun j => -∑ k, Matrix.mulVec (Matrix.transpose (scenT inst k))
              (fun i => pv (Sum.inr (k, i))) j) xstar := by
        simp only [dotProduct, Pi.sub_apply]
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl (fun j _ => by ring)
      rw [hlin]
      ring
  · -- easy direction
    rintro ⟨lam, mu, hmunn, hmux, hsub⟩
    refine le_antisymm ?_ (sInf_le (Set.mem_image_of_mem _ hx))
    refine le_sInf ?_
    rintro z ⟨x, hxK, rfl⟩
    have hAx : Matrix.mulVec inst.A x = inst.b := hxK.1
    have hxnn : ∀ j, 0 ≤ x j := hxK.2
    set eta : Fin n1 → ℝ :=
      fun j => -inst.c j + Matrix.mulVec (Matrix.transpose inst.A) lam j + mu j with heta
    have hsubx := hsub x
    have e2 : dotProduct (Matrix.mulVec (Matrix.transpose inst.A) lam) (x - xstar) = 0 := by
      rw [Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_sub, hAx, hAxs]
      simp
    have e3 : 0 ≤ dotProduct mu (x - xstar) := by
      have hd : dotProduct mu (x - xstar) = dotProduct mu x - dotProduct mu xstar := by
        simp only [dotProduct, Pi.sub_apply]
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl (fun j _ => by ring)
      rw [hd, hmux, sub_zero]
      exact Finset.sum_nonneg (fun j _ => mul_nonneg (hmunn j) (hxnn j))
    have hkey : dotProduct inst.c xstar
        ≤ dotProduct inst.c x + dotProduct eta (x - xstar) := by
      have hc : dotProduct inst.c (x - xstar)
          = dotProduct inst.c x - dotProduct inst.c xstar := by
        simp only [dotProduct, Pi.sub_apply]
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl (fun j _ => by ring)
      have e1 : dotProduct eta (x - xstar) + dotProduct inst.c (x - xstar)
          = dotProduct (Matrix.mulVec (Matrix.transpose inst.A) lam) (x - xstar)
            + dotProduct mu (x - xstar) := by
        simp only [dotProduct, heta, Pi.sub_apply, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl (fun j _ => by ring)
      linarith [e1, e2, e3, hc]
    calc obj inst xstar
        = ((dotProduct inst.c xstar : ℝ) : EReal) + Q inst xstar := rfl
      _ ≤ ((dotProduct inst.c x + dotProduct eta (x - xstar) : ℝ) : EReal) + Q inst xstar :=
          add_le_add (by exact_mod_cast hkey) (le_refl _)
      _ = ((dotProduct inst.c x : ℝ) : EReal)
            + (Q inst xstar + ((dotProduct eta (x - xstar) : ℝ) : EReal)) := by
          rw [EReal.coe_add, add_assoc,
            add_comm (((dotProduct eta (x - xstar) : ℝ) : EReal)) (Q inst xstar)]
      _ ≤ ((dotProduct inst.c x : ℝ) : EReal) + Q inst x := add_le_add (le_refl _) hsubx
      _ = obj inst x := rfl

end StochasticProg.Recourse

/-- Top-level entry point: Birge & Louveaux, Chapter 3, Theorem 9. -/
theorem solution {n1 n2 m1 m2 K : ℕ} (inst : StochasticProg.Recourse.Instance n1 n2 m1 m2 K)
    (hQ : ∀ x k, StochasticProg.Recourse.QVal inst x k ≠ ⊥)
    (hfin : ∃ z0 : ℝ,
      sInf (StochasticProg.Recourse.obj inst '' StochasticProg.Recourse.K1 inst) = (z0 : EReal))
    (xstar : Fin n1 → ℝ) (hx : xstar ∈ StochasticProg.Recourse.K1 inst) :
    (StochasticProg.Recourse.obj inst xstar
        = sInf (StochasticProg.Recourse.obj inst '' StochasticProg.Recourse.K1 inst)) ↔
      ∃ (lam : Fin m1 → ℝ) (mu : Fin n1 → ℝ),
        (∀ i, 0 ≤ mu i) ∧ dotProduct mu xstar = 0 ∧
        (fun j => -inst.c j + Matrix.mulVec (Matrix.transpose inst.A) lam j + mu j) ∈
          StochasticProg.Recourse.subdiffQ inst xstar :=
  StochasticProg.Recourse.thm9_kkt_optimality inst hQ hfin xstar hx
