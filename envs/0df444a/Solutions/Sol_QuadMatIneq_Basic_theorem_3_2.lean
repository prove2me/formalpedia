-- Prove2me | solution 1 for QuadMatIneq.Basic.theorem_3_2
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-20T04:04:33.905929+00:00
-- url     : https://prove2.me/submissions/1aa28a58-35dd-4fe7-ad51-a3f8c318b5e7

-- Licensed under Apache 2.0. Complete native five-clause quadratic matrix inequality geometry.
import Mathlib
import Definitions.Def_QuadMatIneq_Basic_QMI


noncomputable section
namespace QMIProof
open Matrix Filter Topology
open scoped MatrixOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma quadratic_nonneg {A : Matrix ι ι ℝ} (hA : A.PosSemidef) (v : ι → ℝ) :
    0 ≤ v ⬝ᵥ (A *ᵥ v) := by
  simpa only [star_trivial] using hA.dotProduct_mulVec_nonneg v

omit [DecidableEq ι] in
lemma quadratic_zero_iff {A : Matrix ι ι ℝ} (hA : A.PosSemidef) (v : ι → ℝ) :
    v ⬝ᵥ (A *ᵥ v) = 0 ↔ A *ᵥ v = 0 := by
  simpa only [star_trivial] using hA.dotProduct_mulVec_zero_iff v

omit [DecidableEq ι] in
lemma exists_null_of_not_posDef {A : Matrix ι ι ℝ} (hA : A.PosSemidef)
    (hn : ¬ A.PosDef) : ∃ v : ι → ℝ, v ≠ 0 ∧ A *ᵥ v = 0 := by
  by_contra h
  push Not at h
  apply hn
  apply Matrix.PosDef.of_dotProduct_mulVec_pos hA.isHermitian
  intro v hv
  simp only [star_trivial]
  exact lt_of_le_of_ne (quadratic_nonneg hA v)
    (fun he => h v hv ((quadratic_zero_iff hA v).mp he.symm))

lemma exists_positive_quadratic {A : Matrix ι ι ℝ} (hA : A.PosSemidef)
    (hn : A ≠ 0) : ∃ v : ι → ℝ, 0 < v ⬝ᵥ (A *ᵥ v) := by
  by_contra h
  push Not at h
  apply hn
  ext i j
  have hz := (quadratic_zero_iff hA (Pi.single j 1)).mp
    (le_antisymm (h _) (quadratic_nonneg hA _))
  simpa using congrFun hz i

lemma posDef_lower {A : Matrix ι ι ℝ} (hA : A.PosDef) :
    ∃ r : ℝ, 0 < r ∧ (A - r • (1 : Matrix ι ι ℝ)).PosSemidef := by
  cases isEmpty_or_nonempty ι with
  | inl h =>
    let := h
    refine ⟨1, zero_lt_one, ?_⟩
    have he : A - (1 : ℝ) • (1 : Matrix ι ι ℝ) = 0 := Subsingleton.elim _ _
    rw [he]
    exact Matrix.PosSemidef.zero
  | inr h =>
    let := h
    obtain ⟨r, hr, hle⟩ := (CFC.exists_pos_algebraMap_le_iff
      hA.isStrictlyPositive.isSelfAdjoint).2
      (fun z hz => hA.isStrictlyPositive.spectrum_pos hz)
    refine ⟨r, hr, ?_⟩
    simpa only [Matrix.le_iff, Algebra.algebraMap_eq_smul_one] using hle

omit [DecidableEq ι] in
lemma posDef_of_unit_quadratic {A : Matrix ι ι ℝ} (hA : A.IsHermitian)
    (h : ∀ v : ι → ℝ, ‖v‖ = 1 → 0 < v ⬝ᵥ (A *ᵥ v)) : A.PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos hA
  intro v hv
  have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hw : ‖(‖v‖⁻¹ : ℝ) • v‖ = 1 := by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hn.le), inv_mul_cancel₀ hn.ne']
  have hh := h ((‖v‖⁻¹ : ℝ) • v) hw
  simp only [mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul] at hh
  simp only [star_trivial]
  by_contra hneg
  have hle : v ⬝ᵥ (A *ᵥ v) ≤ 0 := le_of_not_gt hneg
  have hi : 0 ≤ ‖v‖⁻¹ := inv_nonneg.mpr hn.le
  have hz := mul_nonpos_of_nonneg_of_nonpos hi (mul_nonpos_of_nonneg_of_nonpos hi hle)
  nlinarith

omit [DecidableEq ι] in
lemma continuous_quadratic :
    Continuous (fun p : Matrix ι ι ℝ × (ι → ℝ) => p.2 ⬝ᵥ (p.1 *ᵥ p.2)) := by
  unfold dotProduct Matrix.mulVec
  fun_prop

omit [DecidableEq ι] in
lemma eventually_posDef_of_continuousAt {α : Type*} [TopologicalSpace α]
    {F : α → Matrix ι ι ℝ} {a : α} (hc : ContinuousAt F a)
    (hs : ∀ b, (F b).IsHermitian) (hp : (F a).PosDef) :
    ∀ᶠ b in 𝓝 a, (F b).PosDef := by
  have he : ∀ᶠ b in 𝓝 a, ∀ v ∈ Metric.sphere (0 : ι → ℝ) 1,
      0 < v ⬝ᵥ (F b *ᵥ v) := by
    apply (isCompact_sphere (0 : ι → ℝ) 1).eventually_forall_of_forall_eventually
    intro v hv
    have hv' : v ≠ 0 := by
      have : ‖v‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using hv
      intro h; simp [h] at this
    have hq : 0 < v ⬝ᵥ (F a *ᵥ v) := by
      simpa only [star_trivial] using hp.dotProduct_mulVec_pos hv'
    have hcont : ContinuousAt (fun p : α × (ι → ℝ) => p.2 ⬝ᵥ (F p.1 *ᵥ p.2)) (a,v) :=
      continuous_quadratic.continuousAt.comp ((hc.comp continuousAt_fst).prodMk continuousAt_snd)
    exact hcont.eventually (lt_mem_nhds hq)
  filter_upwards [he] with b hb
  apply posDef_of_unit_quadratic (hs b)
  intro v hv
  exact hb v (by simpa only [Metric.mem_sphere, dist_zero_right] using hv)

end QMIProof


noncomputable section
namespace QMIProof
open Matrix
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

def centeredForm (A : Matrix κ κ ℝ) (S : Matrix ι ι ℝ) (Y : Matrix κ ι ℝ) :=
  S - Yᵀ * A * Y

def centeredSet (A : Matrix κ κ ℝ) (S : Matrix ι ι ℝ) : Set (Matrix κ ι ℝ) :=
  {Y | (centeredForm A S Y).PosSemidef}

lemma congruence_psd {A : Matrix κ κ ℝ} (hA : A.PosSemidef) (Y : Matrix κ ι ℝ) :
    (Yᵀ * A * Y).PosSemidef := by
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hA.conjTranspose_mul_mul_same Y

lemma centered_hermitian {A : Matrix κ κ ℝ} {S : Matrix ι ι ℝ}
    (hA : A.PosSemidef) (hS : S.PosSemidef) (Y : Matrix κ ι ℝ) :
    (centeredForm A S Y).IsHermitian :=
  hS.isHermitian.sub (congruence_psd hA Y).isHermitian

omit [Fintype ι] in
lemma centered_zero {A : Matrix κ κ ℝ} {S : Matrix ι ι ℝ} (hS : S.PosSemidef) :
    (0 : Matrix κ ι ℝ) ∈ centeredSet A S := by
  simpa [centeredSet, centeredForm] using hS

lemma centered_strict_iff {A : Matrix κ κ ℝ} {S : Matrix ι ι ℝ}
    (hA : A.PosSemidef) :
    (∃ Y : Matrix κ ι ℝ, (centeredForm A S Y).PosDef) ↔ S.PosDef := by
  constructor
  · rintro ⟨Y, hY⟩
    have h := hY.add_posSemidef (congruence_psd hA Y)
    simpa [centeredForm] using h
  · intro hS
    exact ⟨0, by simpa [centeredForm] using hS⟩

omit [Fintype ι] in
lemma centered_combination (A : Matrix κ κ ℝ) (S : Matrix ι ι ℝ)
    (Y W : Matrix κ ι ℝ) {a b : ℝ} (hab : a + b = 1) :
    centeredForm A S (a • Y + b • W) =
      a • centeredForm A S Y + b • centeredForm A S W +
        (a*b) • ((Y-W)ᵀ * A * (Y-W)) := by
  have hb : b = 1-a := by linarith
  subst b
  simp only [centeredForm, transpose_add, transpose_smul, transpose_sub,
    Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub,
    Matrix.smul_mul, Matrix.mul_smul, smul_add, smul_sub, smul_smul]
  module

lemma centered_convex {A : Matrix κ κ ℝ} {S : Matrix ι ι ℝ}
    (hA : A.PosSemidef) : Convex ℝ (centeredSet A S) := by
  intro Y hY W hW a b ha hb hab
  change (centeredForm A S (a • Y+b • W)).PosSemidef
  rw [centered_combination A S Y W hab]
  exact ((hY.smul ha).add (hW.smul hb)).add
    ((congruence_psd hA (Y-W)).smul (mul_nonneg ha hb))

lemma centered_quadratic {A : Matrix κ κ ℝ} {S : Matrix ι ι ℝ}
    {Y : Matrix κ ι ℝ} (hY : Y ∈ centeredSet A S) (v : ι → ℝ) :
    (Y *ᵥ v) ⬝ᵥ (A *ᵥ (Y *ᵥ v)) ≤ v ⬝ᵥ (S *ᵥ v) := by
  have h := quadratic_nonneg hY v
  simp only [centeredForm, sub_mulVec, dotProduct_sub, ← mulVec_mulVec] at h
  have he (w : κ → ℝ) : v ⬝ᵥ (Yᵀ *ᵥ w) = (Y *ᵥ v) ⬝ᵥ w := by
    rw [dotProduct_mulVec, vecMul_transpose]
  rw [he] at h
  linarith

lemma centered_null {A : Matrix κ κ ℝ} {S : Matrix ι ι ℝ}
    (hA : A.PosSemidef) {Y : Matrix κ ι ℝ} (hY : Y ∈ centeredSet A S)
    {v : ι → ℝ} (hv : S *ᵥ v = 0) : A *ᵥ (Y *ᵥ v) = 0 := by
  apply (quadratic_zero_iff hA _).mp
  apply le_antisymm _ (quadratic_nonneg hA _)
  simpa only [hv, dotProduct_zero] using centered_quadratic hY v

end QMIProof


noncomputable section
namespace QMIProof
open Matrix
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

lemma lower_quadratic {A : Matrix κ κ ℝ} {r : ℝ}
    (hr : (A-r • (1 : Matrix κ κ ℝ)).PosSemidef) (v : κ → ℝ) :
    r * ∑ i, (v i)^2 ≤ v ⬝ᵥ (A *ᵥ v) := by
  have h := quadratic_nonneg hr v
  simp only [sub_mulVec, smul_mulVec, one_mulVec, dotProduct_sub,
    dotProduct_smul, smul_eq_mul] at h
  simpa only [dotProduct, ← pow_two] using (sub_nonneg.mp h)

lemma centered_entry_bound {A : Matrix κ κ ℝ} {S : Matrix ι ι ℝ}
    (hA : A.PosDef) : ∃ C : ℝ, ∀ Y ∈ centeredSet A S, ∀ i j, |Y i j| ≤ C := by
  obtain ⟨r, hr, hrA⟩ := posDef_lower hA
  let B : ℝ := ∑ j, |S j j|
  have hB : 0 ≤ B := Finset.sum_nonneg fun _ _ => abs_nonneg _
  refine ⟨Real.sqrt (B/r), ?_⟩
  intro Y hY i j
  have hq := centered_quadratic hY (Pi.single j 1)
  simp only [mulVec_single_one, single_dotProduct, one_mul, Matrix.col_apply] at hq
  change (fun i => Y i j) ⬝ᵥ (A *ᵥ (fun i => Y i j)) ≤ S j j at hq
  have hl := lower_quadratic hrA (fun i => Y i j)
  have hi : (Y i j)^2 ≤ ∑ k, (Y k j)^2 :=
    Finset.single_le_sum (fun k _ => sq_nonneg (Y k j)) (Finset.mem_univ i)
  have hj : S j j ≤ B := le_trans (le_abs_self _)
    (Finset.single_le_sum (fun k _ => abs_nonneg (S k k)) (Finset.mem_univ j))
  have hs : (Y i j)^2 ≤ B/r := (le_div_iff₀ hr).2 (by nlinarith)
  have hsq := Real.sq_sqrt (div_nonneg hB hr.le)
  have hp := Real.sqrt_nonneg (B/r)
  have hab := sq_abs (Y i j)
  nlinarith [abs_nonneg (Y i j)]

omit [Fintype ι] [DecidableEq ι] [DecidableEq κ] in
lemma null_outer_feasible {A : Matrix κ κ ℝ} {S : Matrix ι ι ℝ}
    (hS : S.PosSemidef) {u : κ → ℝ} (hu : A *ᵥ u = 0) (v : ι → ℝ) :
    (fun i j => u i * v j) ∈ centeredSet A S := by
  let W : Matrix κ ι ℝ := fun i j => u i * v j
  have hz : A * W = 0 := by
    ext i j
    change (∑ k, A i k * (u k * v j)) = 0
    simp_rw [← mul_assoc]
    rw [← Finset.sum_mul]
    simpa only [mulVec, dotProduct, Pi.zero_apply, zero_mul] using
      congrArg (fun z : κ → ℝ => z i * v j) hu
  change (S - Wᵀ * A * W).PosSemidef
  rw [Matrix.mul_assoc, hz, Matrix.mul_zero, sub_zero]
  exact hS

lemma centered_bounded_iff [Nonempty ι] {A : Matrix κ κ ℝ} {S : Matrix ι ι ℝ}
    (hA : A.PosSemidef) (hS : S.PosSemidef) :
    (∃ C : ℝ, ∀ Y ∈ centeredSet A S, ∀ i j, |Y i j| ≤ C) ↔ A.PosDef := by
  constructor
  · rintro ⟨C,hC⟩
    by_contra hn
    obtain ⟨u,hu,huA⟩ := exists_null_of_not_posDef hA hn
    have he : ∃ i, u i ≠ 0 := by
      by_contra h
      push Not at h
      exact hu (funext h)
    obtain ⟨i,hi⟩ := he
    let j : ι := Classical.choice inferInstance
    let t : ℝ := (|C|+1)/(u i)
    have h := hC (fun k l => u k * (if l=j then t else 0))
      (null_outer_feasible hS huA (fun l => if l=j then t else 0)) i j
    simp only [ite_true] at h
    have ht : u i*t = |C|+1 := by dsimp [t]; field_simp
    rw [ht, abs_of_pos (by positivity)] at h
    linarith [le_abs_self C]
  · exact centered_entry_bound

end QMIProof


noncomputable section
namespace QMIProof
open Matrix Filter Topology Set
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

omit [DecidableEq ι] [DecidableEq κ] in
lemma centered_interior_of_strict {A : Matrix κ κ ℝ} {S : Matrix ι ι ℝ}
    (hA : A.PosSemidef) (hS : S.PosDef) : (interior (centeredSet A S)).Nonempty := by
  have hc : Continuous (centeredForm A S) := by
    unfold centeredForm
    fun_prop
  have he := eventually_posDef_of_continuousAt hc.continuousAt
    (centered_hermitian hA hS.posSemidef) (a := (0 : Matrix κ ι ℝ))
    (by simpa [centeredForm] using hS)
  refine ⟨0, mem_interior_iff_mem_nhds.mpr ?_⟩
  filter_upwards [he] with Y hY
  exact hY.posSemidef

omit [Fintype κ] [DecidableEq ι] [DecidableEq κ] in
lemma outer_mulVec (u : κ → ℝ) (v : ι → ℝ) :
    (fun i j => u i*v j) *ᵥ v = (∑ j, (v j)^2) • u := by
  ext i
  simp only [mulVec, dotProduct, Pi.smul_apply, smul_eq_mul]
  simp_rw [mul_assoc, ← pow_two, ← Finset.mul_sum]
  ring

omit [DecidableEq ι] in
lemma centered_interior_iff {A : Matrix κ κ ℝ} {S : Matrix ι ι ℝ}
    (hA : A.PosSemidef) (hS : S.PosSemidef) :
    (interior (centeredSet A S)).Nonempty ↔ A = 0 ∨ S.PosDef := by
  constructor
  · rintro ⟨Y,hY⟩
    by_cases ha : A=0
    · exact Or.inl ha
    right
    by_contra hs
    obtain ⟨v,hv,hvS⟩ := exists_null_of_not_posDef hS hs
    obtain ⟨u,hu⟩ := exists_positive_quadratic hA ha
    have hY0 : Y ∈ centeredSet A S := interior_subset hY
    have hzero := centered_null hA hY0 hvS
    let W : Matrix κ ι ℝ := fun i j => u i*v j
    have hc : ContinuousAt (fun t : ℝ => Y+t • W) 0 := by fun_prop
    have hev : ∀ᶠ t : ℝ in 𝓝 0, Y+t • W ∈ centeredSet A S := by
      have hn := mem_interior_iff_mem_nhds.mp hY
      have hc' : Tendsto (fun t : ℝ => Y+t • W) (𝓝 0) (𝓝 Y) := by
        simpa using hc.tendsto
      exact hc'.eventually hn
    obtain ⟨ε,hε,hεmem⟩ := Metric.eventually_nhds_iff.mp hev
    have ht : Y+(ε/2) • W ∈ centeredSet A S := hεmem (by
      simp only [dist_zero_right, Real.norm_eq_abs, abs_of_pos (half_pos hε)]
      linarith)
    have hz := centered_null hA ht hvS
    have hW : W *ᵥ v = (∑ j, (v j)^2) • u := outer_mulVec u v
    rw [add_mulVec, smul_mulVec, hW, mulVec_add, mulVec_smul,
      mulVec_smul, hzero, zero_add] at hz
    have hvsum : 0 < ∑ j, (v j)^2 := by
      apply Finset.sum_pos' (fun j _ => sq_nonneg (v j))
      have he : ∃ j, v j ≠ 0 := by
        by_contra h
        push Not at h
        exact hv (funext h)
      obtain ⟨j,hj⟩ := he
      exact ⟨j, Finset.mem_univ j, sq_pos_of_ne_zero hj⟩
    have hu0 : A *ᵥ u = 0 := by
      exact (smul_eq_zero.mp (smul_eq_zero.mp hz |>.resolve_left (ne_of_gt (half_pos hε))))
        |>.resolve_left (ne_of_gt hvsum)
    rw [hu0, dotProduct_zero] at hu
    exact lt_irrefl 0 hu
  · rintro (rfl|hS')
    · have he : centeredSet (0 : Matrix κ κ ℝ) S = Set.univ := by
        ext Y
        simp [centeredSet, centeredForm, hS]
      rw [he, interior_univ]
      exact Set.univ_nonempty
    · exact centered_interior_of_strict hA hS'

end QMIProof


noncomputable section
namespace QMIProof
open Matrix Set
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

omit [DecidableEq ι] [DecidableEq κ] in
lemma entrywise_translation (K : Set (Matrix κ ι ℝ)) (C : Matrix κ ι ℝ) :
    (∃ b : ℝ, ∀ Z, Z+C ∈ K → ∀ i j, |Z i j| ≤ b) ↔
      (∃ b : ℝ, ∀ Y ∈ K, ∀ i j, |Y i j| ≤ b) := by
  have hc (i : κ) (j : ι) : |C i j| ≤ ∑ k, ∑ l, |C k l| :=
    le_trans (Finset.single_le_sum (fun l _ => abs_nonneg (C i l)) (Finset.mem_univ j))
      (Finset.single_le_sum (fun k _ => Finset.sum_nonneg fun l _ => abs_nonneg (C k l))
        (Finset.mem_univ i))
  constructor
  · rintro ⟨b,hb⟩
    refine ⟨b+∑ k, ∑ l, |C k l|, ?_⟩
    intro Y hY i j
    have h := hb (Y-C) (by simpa using hY) i j
    have ha := abs_add_le ((Y-C) i j) (C i j)
    have he : (Y-C) i j+C i j=Y i j := by simp
    rw [he] at ha
    exact ha.trans (add_le_add h (hc i j))
  · rintro ⟨b,hb⟩
    refine ⟨b+∑ k, ∑ l, |C k l|, ?_⟩
    intro Z hZ i j
    have h := hb (Z+C) hZ i j
    have ha := abs_sub ((Z+C) i j) (C i j)
    have he : (Z+C) i j-C i j=Z i j := by simp
    rw [he] at ha
    exact ha.trans (add_le_add h (hc i j))

omit [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] in
lemma interior_translation (K : Set (Matrix κ ι ℝ)) (C : Matrix κ ι ℝ) :
    (interior {Z : Matrix κ ι ℝ | Z+C ∈ K}).Nonempty ↔ (interior K).Nonempty := by
  have he := (Homeomorph.addRight C).preimage_interior K
  change (interior ((Homeomorph.addRight C) ⁻¹' K)).Nonempty ↔ _
  rw [← he]
  exact (Homeomorph.addRight C).surjective.nonempty_preimage

omit [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] in
lemma convex_translation {K : Set (Matrix κ ι ℝ)} (hK : Convex ℝ K)
    (C : Matrix κ ι ℝ) : Convex ℝ {Z : Matrix κ ι ℝ | Z+C ∈ K} := by
  intro Z hZ W hW a b ha hb hab
  have h := hK hZ hW ha hb hab
  change a • Z+b • W+C ∈ K
  have he : a • (Z+C)+b • (W+C)=a • Z+b • W+C := by
    rw [smul_add, smul_add]
    have hc : a • C+b • C=C := by rw [← add_smul, hab, one_smul]
    calc
      _ = a • Z+b • W+(a • C+b • C) := by abel
      _ = _ := by rw [hc]
  rw [← he]
  exact h

end QMIProof


namespace QMIProof
open Matrix QuadMatIneq.Basic

 theorem penrose_unique {a b : Type*} [Fintype a] [Fintype b]
    {A : Matrix a b ℝ} {X Y : Matrix b a ℝ}
    (hX : IsMoorePenrose A X) (hY : IsMoorePenrose A Y) : X = Y := by
  obtain ⟨hx1, hx2, hx3, hx4⟩ := hX
  obtain ⟨hy1, hy2, hy3, hy4⟩ := hY
  have hxy : (A * X) * (A * Y) = A * Y := by
    rw [← Matrix.mul_assoc, hx1]
  have hyx : (A * Y) * (A * X) = A * X := by
    rw [← Matrix.mul_assoc, hy1]
  have ht := congrArg Matrix.transpose hxy
  simp only [transpose_mul, hx3, hy3] at ht
  have hleft : A * X = A * Y := hyx.symm.trans ht
  have hxy' : (X * A) * (Y * A) = X * A := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc A Y A, hy1]
  have hyx' : (Y * A) * (X * A) = Y * A := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc A X A, hx1]
  have ht' := congrArg Matrix.transpose hxy'
  simp only [transpose_mul, hx4, hy4] at ht'
  have hright : X * A = Y * A := ht'.symm.trans hyx'
  calc
    X = X * A * X := hx2.symm
    _ = X * A * Y := by rw [Matrix.mul_assoc, hleft, ← Matrix.mul_assoc]
    _ = Y * A * Y := by rw [hright]
    _ = Y := hy2

 theorem penrose_diagonal {n : Type*} [Fintype n] [DecidableEq n] (d : n → ℝ) :
    IsMoorePenrose (diagonal d) (diagonal fun i => (d i)⁻¹) := by
  unfold IsMoorePenrose
  simp only [diagonal_mul_diagonal, diagonal_transpose]
  refine ⟨?_, ?_, trivial, trivial⟩
  · congr 1; funext i; by_cases hi : d i = 0 <;> simp [hi]
  · congr 1; funext i; by_cases hi : d i = 0 <;> simp [hi]

 theorem penrose_conjugate {n : Type*} [Fintype n] [DecidableEq n]
    (U A X : Matrix n n ℝ) (hU : Uᵀ * U = 1) (h : IsMoorePenrose A X) :
    IsMoorePenrose (U * A * Uᵀ) (U * X * Uᵀ) := by
  have hm (B C : Matrix n n ℝ) :
      (U * B * Uᵀ) * (U * C * Uᵀ) = U * (B * C) * Uᵀ := by
    simp only [Matrix.mul_assoc, ← Matrix.mul_assoc Uᵀ U, hU, one_mul]
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hm, hm, h1]
  · rw [hm, hm, h2]
  · rw [hm, transpose_mul, transpose_transpose, transpose_mul, h3]
    simp only [Matrix.mul_assoc]
  · rw [hm, transpose_mul, transpose_transpose, transpose_mul, h4]
    simp only [Matrix.mul_assoc]

end QMIProof


namespace QMIProof
open Matrix QuadMatIneq.Basic
variable {n : Type*} [Fintype n] [DecidableEq n]

 theorem spectral_real {A : Matrix n n ℝ} (hA : A.IsHermitian) :
    ∃ U : Matrix n n ℝ, Uᵀ * U = 1 ∧ U * Uᵀ = 1 ∧
      A = U * diagonal hA.eigenvalues * Uᵀ := by
  refine ⟨hA.eigenvectorUnitary, ?_, ?_, ?_⟩
  · simpa only [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] using
      Unitary.coe_star_mul_self hA.eigenvectorUnitary
  · simpa only [Unitary.coe_star, star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] using
      Unitary.coe_mul_star_self hA.eigenvectorUnitary
  · simpa only [Unitary.conjStarAlgAut_apply, star_eq_conjTranspose,
      conjTranspose_eq_transpose_of_trivial, RCLike.ofReal_real_eq_id, Function.id_comp] using hA.spectral_theorem

 theorem pinv_spectral {A : Matrix n n ℝ} (hA : A.IsHermitian) :
    ∃ U : Matrix n n ℝ, Uᵀ * U = 1 ∧ U * Uᵀ = 1 ∧
      A = U * diagonal hA.eigenvalues * Uᵀ ∧
      pinv A = U * diagonal (fun i => (hA.eigenvalues i)⁻¹) * Uᵀ := by
  obtain ⟨U, hu, hu', ha⟩ := spectral_real hA
  have hw : IsMoorePenrose A (U * diagonal (fun i => (hA.eigenvalues i)⁻¹) * Uᵀ) := by
    conv_lhs => rw [ha]
    exact penrose_conjugate U _ _ hu (penrose_diagonal _)
  have hp : IsMoorePenrose A (pinv A) := Classical.epsilon_spec ⟨_, hw⟩
  exact ⟨U, hu, hu', ha, penrose_unique hp hw⟩

 theorem pinv_spec {A : Matrix n n ℝ} (hA : A.IsHermitian) :
    IsMoorePenrose A (pinv A) := by
  obtain ⟨U, hu, _, ha, hp⟩ := pinv_spectral hA
  rw [hp]
  conv_lhs => rw [ha]
  exact penrose_conjugate U _ _ hu (penrose_diagonal _)

 theorem pinv_transpose {A : Matrix n n ℝ} (hA : A.IsHermitian) :
    (pinv A)ᵀ = pinv A := by
  obtain ⟨U, _, _, _, hp⟩ := pinv_spectral hA
  rw [hp]
  simp only [transpose_mul, transpose_transpose, diagonal_transpose, mul_assoc]

 theorem pinv_commute {A : Matrix n n ℝ} (hA : A.IsHermitian) :
    A * pinv A = pinv A * A := by
  have hp := pinv_spec hA
  have ht := hp.2.2.1
  rw [transpose_mul, pinv_transpose hA] at ht
  have ha : Aᵀ = A := by simpa only [IsHermitian, conjTranspose_eq_transpose_of_trivial] using hA
  rw [ha] at ht
  exact ht.symm

end QMIProof


namespace QMIProof
open Matrix QuadMatIneq.Basic
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

omit [Fintype ι] [DecidableEq ι] in
lemma kernel_pinv_right (C : Matrix ι κ ℝ) {D : Matrix κ κ ℝ}
    (hD : D.IsHermitian) (hker : ∀ v, D *ᵥ v = 0 → C *ᵥ v = 0) :
    C * pinv D * D = C := by
  apply Matrix.mulVec_injective
  funext v
  have hz : D *ᵥ (v - pinv D *ᵥ (D *ᵥ v)) = 0 := by
    simp only [mulVec_sub, mulVec_mulVec, ← Matrix.mul_assoc, (pinv_spec hD).1, sub_self]
  have hc := hker _ hz
  simp only [mulVec_sub, mulVec_mulVec, ← Matrix.mul_assoc] at hc
  exact (sub_eq_zero.mp hc).symm

omit [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] in
lemma qmi_blocks {P : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ} (hP : P.IsHermitian) :
    P.toBlocks₂₂.IsHermitian ∧ P.toBlocks₁₂ᵀ = P.toBlocks₂₁ ∧
      P.toBlocks₂₁ᵀ = P.toBlocks₁₂ := by
  have h := hP
  rw [← Matrix.fromBlocks_toBlocks P, isHermitian_fromBlocks_iff] at h
  exact ⟨h.2.2.2, by simpa only [conjTranspose_eq_transpose_of_trivial] using h.2.1,
    by simpa only [conjTranspose_eq_transpose_of_trivial] using h.2.2.1⟩

omit [DecidableEq κ] in
lemma qmiForm_expansion (P : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ) (Z : Matrix κ ι ℝ) :
    qmiForm P Z = P.toBlocks₁₁ + Zᵀ * P.toBlocks₂₁ +
      P.toBlocks₁₂ * Z + Zᵀ * P.toBlocks₂₂ * Z := by
  unfold qmiForm
  conv_lhs => rw [← Matrix.fromBlocks_toBlocks P]
  simp only [transpose_fromRows, transpose_one, fromCols_mul_fromBlocks,
    fromCols_mul_fromRows, Matrix.one_mul, Matrix.mul_one, Matrix.add_mul]
  abel

lemma qmi_completion (P : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ) (hP : InPi P)
    (Z : Matrix κ ι ℝ) :
    qmiForm P Z = schur P -
      (Z + pinv P.toBlocks₂₂ * P.toBlocks₂₁)ᵀ * (-P.toBlocks₂₂) *
        (Z + pinv P.toBlocks₂₂ * P.toBlocks₂₁) := by
  obtain ⟨hd, hc, hc'⟩ := qmi_blocks hP.1
  have hr := kernel_pinv_right P.toBlocks₁₂ hd hP.2.2.2
  have hl : P.toBlocks₂₂ * pinv P.toBlocks₂₂ * P.toBlocks₂₁ = P.toBlocks₂₁ := by
    have ht := congrArg Matrix.transpose hr
    have hd' : P.toBlocks₂₂ᵀ = P.toBlocks₂₂ := by
      simpa only [IsHermitian, conjTranspose_eq_transpose_of_trivial] using hd
    simpa only [transpose_mul, pinv_transpose hd, hc, hd', Matrix.mul_assoc] using ht
  rw [qmiForm_expansion]
  unfold schur
  simp only [transpose_add, transpose_mul, pinv_transpose hd, hc',
    Matrix.add_mul, Matrix.mul_add, Matrix.mul_neg, Matrix.neg_mul,
    ← Matrix.mul_assoc, hr]
  simp only [Matrix.mul_assoc] at hl
  simp only [Matrix.mul_assoc, hl]
  abel

end QMIProof


namespace QMIProof
open Matrix
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

omit [Fintype ι] in
lemma diagonal_rank_factorization (a : κ → ℝ) (s : ι → ℝ)
    (ha : ∀ k, 0 ≤ a k) (hs : ∀ i, 0 ≤ s i)
    (f : {i // s i ≠ 0} ↪ {k // a k ≠ 0}) :
    ∃ W : Matrix κ ι ℝ, Wᵀ * diagonal a * W = diagonal s := by
  classical
  let W : Matrix κ ι ℝ := fun k i =>
    if hi : s i ≠ 0 then if k = (f ⟨i, hi⟩).val then Real.sqrt (s i / a k) else 0 else 0
  refine ⟨W, ?_⟩
  ext i j
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, transpose_apply]
  by_cases hi : s i = 0
  · simp [W, hi, diagonal_apply]
  · let k : κ := (f ⟨i, hi⟩).val
    have hak : a k ≠ 0 := (f ⟨i, hi⟩).property
    rw [Finset.sum_eq_single k]
    · by_cases hij : i = j
      · subst j
        have hsq := Real.sq_sqrt (div_nonneg (hs i) (ha k))
        simp only [diagonal_apply_eq]
        have hk : k = (f ⟨i, hi⟩).val := rfl
        simp only [W, dif_pos hi, if_pos hk]
        change Real.sqrt (s i / a k) * a k * Real.sqrt (s i / a k) = s i
        calc
          _ = a k * (Real.sqrt (s i / a k)) ^ 2 := by ring
          _ = s i := by rw [hsq]; field_simp [hak]
      · have hz : W k j = 0 := by
          by_cases hj : s j = 0
          · simp [W, hj]
          · have hne : k ≠ (f ⟨j, hj⟩).val := by
              intro he
              have hh : (⟨i, hi⟩ : {i // s i ≠ 0}) = ⟨j, hj⟩ :=
                f.injective (Subtype.ext he)
              exact hij (congrArg Subtype.val hh)
            simp only [W, dif_pos hj, if_neg hne]
        rw [hz, mul_zero, diagonal_apply_ne _ hij]
    · intro b _ hbk
      have hbi : W b i = 0 := by simp [W, hi, k, hbk]
      rw [hbi, zero_mul, zero_mul]
    · intro hk
      exact False.elim (hk (Finset.mem_univ k))

end QMIProof


namespace QMIProof
open Matrix
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

lemma psd_rank_factorization {A : Matrix κ κ ℝ} {S : Matrix ι ι ℝ}
    (hA : A.PosSemidef) (hS : S.PosSemidef) (hr : S.rank ≤ A.rank) :
    ∃ Y : Matrix κ ι ℝ, Yᵀ * A * Y = S := by
  classical
  have hc : Fintype.card {i // hS.isHermitian.eigenvalues i ≠ 0} ≤
      Fintype.card {k // hA.isHermitian.eigenvalues k ≠ 0} := by
    simpa only [hS.isHermitian.rank_eq_card_non_zero_eigs,
      hA.isHermitian.rank_eq_card_non_zero_eigs] using hr
  obtain ⟨f⟩ := Function.Embedding.nonempty_of_card_le hc
  obtain ⟨W, hw⟩ := diagonal_rank_factorization hA.isHermitian.eigenvalues
    hS.isHermitian.eigenvalues hA.eigenvalues_nonneg hS.eigenvalues_nonneg f
  obtain ⟨U, _hu, _hu', hsu⟩ := spectral_real hS.isHermitian
  obtain ⟨V, hv, _hv', hav⟩ := spectral_real hA.isHermitian
  refine ⟨V * W * Uᵀ, ?_⟩
  rw [hav, hsu]
  simp only [transpose_mul, transpose_transpose, Matrix.mul_assoc]
  simp only [← Matrix.mul_assoc Vᵀ V, hv, Matrix.one_mul]
  calc
    _ = U * (Wᵀ * diagonal hA.isHermitian.eigenvalues * W) * Uᵀ := by
      simp only [Matrix.mul_assoc]
    _ = _ := by rw [hw]; simp only [Matrix.mul_assoc]

end QMIProof


noncomputable section
namespace QMIProof
open Matrix QuadMatIneq.Basic Set
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

lemma native_centered (P : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ) (hP : InPi P)
    (Z : Matrix κ ι ℝ) : qmiForm P Z =
      centeredForm (-P.toBlocks₂₂) (schur P) (Z+pinv P.toBlocks₂₂*P.toBlocks₂₁) :=
  qmi_completion P hP Z

lemma native_set (P : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ) (hP : InPi P) :
    ZSet P = {Z | Z+pinv P.toBlocks₂₂*P.toBlocks₂₁ ∈ centeredSet (-P.toBlocks₂₂) (schur P)} := by
  ext Z
  simp only [ZSet, Set.mem_ofPred_eq, centeredSet, native_centered P hP]

lemma native_nonempty_convex (P : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ) (hP : InPi P) :
    (ZSet P).Nonempty ∧ Convex ℝ (ZSet P) := by
  rw [native_set P hP]
  constructor
  · refine ⟨-(pinv P.toBlocks₂₂*P.toBlocks₂₁), ?_⟩
    simpa using centered_zero (A := -P.toBlocks₂₂) hP.2.2.1
  · exact convex_translation (centered_convex hP.2.1) _

lemma native_bounded (P : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ) (hP : InPi P) [Nonempty ι] :
    (∃ C : ℝ, ∀ Z ∈ ZSet P, ∀ i j, |Z i j| ≤ C) ↔ (-P.toBlocks₂₂).PosDef := by
  rw [native_set P hP]
  exact (entrywise_translation _ _).trans (centered_bounded_iff hP.2.1 hP.2.2.1)

lemma native_interior (P : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ) (hP : InPi P) :
    (interior (ZSet P)).Nonempty ↔ P.toBlocks₂₂=0 ∨ (schur P).PosDef := by
  rw [native_set P hP, interior_translation, centered_interior_iff hP.2.1 hP.2.2.1]
  simp only [neg_eq_zero]

lemma native_strict (P : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ) (hP : InPi P) :
    (ZPlus P).Nonempty ↔ (schur P).PosDef := by
  rw [← centered_strict_iff (S := schur P) hP.2.1]
  constructor
  · rintro ⟨Z,hZ⟩
    exact ⟨Z+pinv P.toBlocks₂₂*P.toBlocks₂₁, by
      simpa only [ZPlus, Set.mem_ofPred_eq, native_centered P hP] using hZ⟩
  · rintro ⟨Y,hY⟩
    refine ⟨Y-pinv P.toBlocks₂₂*P.toBlocks₂₁, ?_⟩
    change (qmiForm P _).PosDef
    rw [native_centered P hP, sub_add_cancel]
    exact hY

end QMIProof


noncomputable section
namespace QMIProof
open Matrix QuadMatIneq.Basic
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

lemma native_zero_iff (P : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ) (hP : InPi P) :
    (ZZero P).Nonempty ↔ (schur P).rank ≤ P.toBlocks₂₂.rank := by
  have hneg : (-P.toBlocks₂₂).rank = P.toBlocks₂₂.rank := by
    simpa only [neg_one_smul] using Matrix.rank_smul_of_mem_nonZeroDivisors
      P.toBlocks₂₂ (c := (-1 : ℝ)) (by simp)
  constructor
  · rintro ⟨Z,hZ⟩
    change qmiForm P Z=0 at hZ
    rw [qmi_completion P hP Z, sub_eq_zero] at hZ
    rw [hZ]
    calc
      _ ≤ ((Z+pinv P.toBlocks₂₂*P.toBlocks₂₁)ᵀ * (-P.toBlocks₂₂)).rank :=
        Matrix.rank_mul_le_left _ _
      _ ≤ (-P.toBlocks₂₂).rank := Matrix.rank_mul_le_right _ _
      _ = P.toBlocks₂₂.rank := hneg
  · intro hr
    have hr' : (schur P).rank ≤ (-P.toBlocks₂₂).rank := by simpa only [hneg] using hr
    obtain ⟨Y,hY⟩ := psd_rank_factorization hP.2.1 hP.2.2.1 hr'
    refine ⟨Y-pinv P.toBlocks₂₂*P.toBlocks₂₁, ?_⟩
    change qmiForm P _=0
    rw [qmi_completion P hP, sub_add_cancel, hY, sub_self]

end QMIProof


namespace QMIProof
open QuadMatIneq.Basic
open Matrix
theorem full_native_geometry {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (P : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ) (hP : InPi P) :
    -- (a) nonempty and convex
    ((ZSet P).Nonempty ∧ Convex ℝ (ZSet P)) ∧
    -- (b) bounded iff Π₂₂ < 0 (for q ⩾ 1)
    (Nonempty ι → ((∃ C : ℝ, ∀ Z ∈ ZSet P, ∀ i j, |Z i j| ≤ C) ↔ (-P.toBlocks₂₂).PosDef)) ∧
    -- (c) nonempty interior iff Π₂₂ = 0 or Π|Π₂₂ > 0
    ((interior (ZSet P)).Nonempty ↔ P.toBlocks₂₂ = 0 ∨ (schur P).PosDef) ∧
    -- (d) 𝒵_r^+(Π) nonempty iff Π|Π₂₂ > 0
    ((ZPlus P).Nonempty ↔ (schur P).PosDef) ∧
    -- (e) 𝒵_r^0(Π) nonempty iff rank Π₂₂ ⩾ rank Π|Π₂₂
    ((ZZero P).Nonempty ↔ (schur P).rank ≤ P.toBlocks₂₂.rank) := by
  refine ⟨native_nonempty_convex P hP, ?_, native_interior P hP,
    native_strict P hP, native_zero_iff P hP⟩
  intro h
  let := h
  exact native_bounded P hP
end QMIProof



open Matrix QuadMatIneq.Basic

namespace QuadMatIneq.Basic
open Matrix
theorem theorem_3_2 {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (P : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ) (hP : InPi P) :
    -- (a) nonempty and convex
    ((ZSet P).Nonempty ∧ Convex ℝ (ZSet P)) ∧
    -- (b) bounded iff Π₂₂ < 0 (for q ⩾ 1)
    (Nonempty ι → ((∃ C : ℝ, ∀ Z ∈ ZSet P, ∀ i j, |Z i j| ≤ C) ↔ (-P.toBlocks₂₂).PosDef)) ∧
    -- (c) nonempty interior iff Π₂₂ = 0 or Π|Π₂₂ > 0
    ((interior (ZSet P)).Nonempty ↔ P.toBlocks₂₂ = 0 ∨ (schur P).PosDef) ∧
    -- (d) 𝒵_r^+(Π) nonempty iff Π|Π₂₂ > 0
    ((ZPlus P).Nonempty ↔ (schur P).PosDef) ∧
    -- (e) 𝒵_r^0(Π) nonempty iff rank Π₂₂ ⩾ rank Π|Π₂₂
    ((ZZero P).Nonempty ↔ (schur P).rank ≤ P.toBlocks₂₂.rank) := by
  exact QMIProof.full_native_geometry P hP
end QuadMatIneq.Basic

open Matrix QuadMatIneq.Basic

theorem solution {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (P : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ) (hP : InPi P) :
    -- (a) nonempty and convex
    ((ZSet P).Nonempty ∧ Convex ℝ (ZSet P)) ∧
    -- (b) bounded iff Π₂₂ < 0 (for q ⩾ 1)
    (Nonempty ι → ((∃ C : ℝ, ∀ Z ∈ ZSet P, ∀ i j, |Z i j| ≤ C) ↔ (-P.toBlocks₂₂).PosDef)) ∧
    -- (c) nonempty interior iff Π₂₂ = 0 or Π|Π₂₂ > 0
    ((interior (ZSet P)).Nonempty ↔ P.toBlocks₂₂ = 0 ∨ (schur P).PosDef) ∧
    -- (d) 𝒵_r^+(Π) nonempty iff Π|Π₂₂ > 0
    ((ZPlus P).Nonempty ↔ (schur P).PosDef) ∧
    -- (e) 𝒵_r^0(Π) nonempty iff rank Π₂₂ ⩾ rank Π|Π₂₂
    ((ZZero P).Nonempty ↔ (schur P).rank ≤ P.toBlocks₂₂.rank) := QuadMatIneq.Basic.theorem_3_2 P hP
