-- Prove2me | solution 1 for RealTimeIter.Contract.theorem_4_1
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-27T02:27:28.071068+00:00
-- url     : https://prove2.me/submissions/524f39aa-adf4-4922-a193-65fa20612cd4

import Mathlib
import Definitions.Def_RealTimeIter_Contract_Problem
import Definitions.Def_RealTimeIter_Contract_Iteration


-- RTIProof.ProjectionCoordinates

noncomputable section
namespace RealTimeIter.Contract.RTIFresh
open scoped InnerProductSpace

@[simp] theorem pull_apply {ι ι' : Type} [Fintype ι] [Fintype ι']
    (g : ι' → Option ι) (y : EuclideanSpace ℝ ι) (j : ι') :
    pull g y j = match g j with | some i => y i | none => 0 := rfl

@[simp] theorem proj_apply (P : OCP) (k : ℕ) (y : PD P k)
    (c : {c : Coord P // k + 1 ≤ stage c}) :
    proj P k y c = y ⟨c.1, Nat.le_of_succ_le c.2⟩ := rfl

@[simp] theorem projTo_apply (P : OCP) (k : ℕ) (y : PD P 0)
    (c : {c : Coord P // k ≤ stage c}) :
    projTo P k y c = y ⟨c.1, Nat.zero_le _⟩ := rfl

 theorem projT_apply (P : OCP) (k : ℕ) (y : PD P (k + 1))
    (c : {c : Coord P // k ≤ stage c}) :
    projT P k y c = if h : k + 1 ≤ stage c.1 then y ⟨c.1, h⟩ else 0 := by
  unfold projT
  rw [pull_apply]
  split_ifs <;> rfl

 theorem liftFrom_apply (P : OCP) (k : ℕ) (y : PD P k)
    (c : {c : Coord P // 0 ≤ stage c}) :
    liftFrom P k y c = if h : k ≤ stage c.1 then y ⟨c.1, h⟩ else 0 := by
  unfold liftFrom
  rw [pull_apply]
  split_ifs <;> rfl

@[simp] theorem proj_projT (P : OCP) (k : ℕ) (y : PD P (k + 1)) :
    proj P k (projT P k y) = y := by
  ext c
  simp only [proj_apply, projT_apply, dif_pos c.2]

@[simp] theorem projTo_liftFrom (P : OCP) (k : ℕ) (y : PD P k) :
    projTo P k (liftFrom P k y) = y := by
  ext c
  simp only [projTo_apply, liftFrom_apply, dif_pos c.2]

@[simp] theorem projTo_zero (P : OCP) (y : PD P 0) : projTo P 0 y = y := by
  ext c
  rfl

@[simp] theorem liftFrom_zero (P : OCP) (y : PD P 0) : liftFrom P 0 y = y := by
  ext c
  simp only [liftFrom_apply, dif_pos (Nat.zero_le _)]

 theorem projTo_succ (P : OCP) (k : ℕ) (y : PD P 0) :
    projTo P (k + 1) y = proj P k (projTo P k y) := by
  ext c
  rfl

 theorem liftFrom_succ (P : OCP) (k : ℕ) (y : PD P (k + 1)) :
    liftFrom P (k + 1) y = liftFrom P k (projT P k y) := by
  ext c
  simp only [liftFrom_apply, projT_apply]
  split_ifs <;> first | rfl | omega

 theorem Dset_eq_image (P : OCP) (D0 : Set (PD P 0)) (k : ℕ) :
    Dset P D0 k = projTo P k '' D0 := by
  induction k with
  | zero => simp [Dset]
  | succ k ih =>
    rw [Dset, ih, Set.image_image]
    congr 1

 theorem proj_inner_projT (P : OCP) (k : ℕ) (x : PD P k) (y : PD P (k + 1)) :
    ⟪proj P k x, y⟫_ℝ = ⟪x, projT P k y⟫_ℝ := by
  classical
  simp only [PiLp.inner_apply, Real.inner_apply]
  let S : Finset {c : Coord P // k ≤ stage c} :=
    Finset.univ.filter (fun c => k + 1 ≤ stage c.1)
  calc
    _ = ∑ c ∈ S, x c * (projT P k y) c := by
      apply Finset.sum_bij (fun c _ => ⟨c.1, Nat.le_of_succ_le c.2⟩)
      · intro c hc
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, c.2⟩
      · intro a ha b hb hab
        apply Subtype.ext
        exact congrArg (fun c : {c : Coord P // k ≤ stage c} => c.1) hab
      · intro b hb
        have h := (Finset.mem_filter.mp hb).2
        exact ⟨⟨b.1, h⟩, Finset.mem_univ _, rfl⟩
      · intro c hc
        simp only [proj_apply, projT_apply, dif_pos c.2]
    _ = _ := by
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro c hc hn
      have h : ¬k + 1 ≤ stage c.1 := by simpa [S] using hn
      simp only [projT_apply, dif_neg h, mul_zero]

end RealTimeIter.Contract.RTIFresh
end

-- RTIProof.CompatibleNorms

noncomputable section
namespace RealTimeIter.Contract.RTIFresh
variable {P : OCP} (ν : CompatNorms P) (k : ℕ)

theorem supplied_zero : ν.nrm k 0 = 0 := by
  simpa using ν.smul k 0 (0 : PD P k)

theorem supplied_neg (x : PD P k) : ν.nrm k (-x) = ν.nrm k x := by
  simpa using ν.smul k (-1) x

def suppliedSeminorm : Seminorm ℝ (PD P k) where
  toFun := ν.nrm k
  map_zero' := supplied_zero ν k
  add_le' := ν.triangle k
  neg' := supplied_neg ν k
  smul' := by intro c x; simpa only [Real.norm_eq_abs] using ν.smul k c x

theorem supplied_nonneg (x : PD P k) : 0 ≤ ν.nrm k x := by
  have h := ν.triangle k x (-x)
  rw [add_neg_cancel, supplied_zero, supplied_neg] at h
  linarith

theorem supplied_pos {x : PD P k} (hx : x ≠ 0) : 0 < ν.nrm k x :=
  lt_of_le_of_ne (supplied_nonneg ν k x) (Ne.symm fun h => hx (ν.eq_zero k x h))

theorem supplied_continuous : Continuous (ν.nrm k) := by
  have hc := (suppliedSeminorm ν k).convexOn.continuousOn isOpen_univ
  exact continuousOn_univ.mp hc

theorem supplied_sub_le (x y : PD P k) : ν.nrm k (x - y) ≤ ν.nrm k x + ν.nrm k y := by
  simpa only [sub_eq_add_neg, supplied_neg] using ν.triangle k x (-y)

theorem supplied_sub_rev (x y : PD P k) : ν.nrm k (x - y) = ν.nrm k (y - x) := by
  rw [← neg_sub x y, supplied_neg]

theorem supplied_sum_le {ι : Type*} (s : Finset ι) (f : ι → PD P k) :
    ν.nrm k (∑ i ∈ s, f i) ≤ ∑ i ∈ s, ν.nrm k (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [supplied_zero]
  | @insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (ν.triangle k _ _).trans (add_le_add le_rfl ih)

end RealTimeIter.Contract.RTIFresh
end

-- RTIProof.ProjectedBalls

noncomputable section
namespace RealTimeIter.Contract.RTIFresh
variable {P : OCP} (ν : CompatNorms P)

theorem supplied_liftFrom (k : ℕ) (y : PD P k) :
    ν.nrm 0 (liftFrom P k y) = ν.nrm k y := by
  induction k with
  | zero => rw [liftFrom_zero]
  | succ k ih => rw [liftFrom_succ, ih, ν.projT_eq]

theorem supplied_projTo (k : ℕ) (y : PD P 0) :
    ν.nrm k (projTo P k y) ≤ ν.nrm 0 y := by
  induction k with
  | zero => simp only [projTo_zero, le_refl]
  | succ k ih =>
    rw [projTo_succ]
    exact (ν.proj_le k _).trans ih

theorem projected_closedBall (k : ℕ) (y0 : PD P 0) (R : ℝ) :
    projTo P k '' {y | ν.nrm 0 (y - y0) ≤ R} =
      {z | ν.nrm k (z - projTo P k y0) ≤ R} := by
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hi := supplied_projTo ν k (y - y0)
    rw [map_sub] at hi
    exact hi.trans hy
  · intro hz
    refine ⟨y0 + liftFrom P k (z - projTo P k y0), ?_, ?_⟩
    · change ν.nrm 0 (y0 + liftFrom P k (z - projTo P k y0) - y0) ≤ R
      change ν.nrm k (z - projTo P k y0) ≤ R at hz
      simpa only [add_sub_cancel_left, supplied_liftFrom] using hz
    · simp only [map_add, projTo_liftFrom, add_sub_cancel]

theorem projected_ball_domain (x0 : Vec P.nx) (y0 : PD P 0)
    (D0 : Set (PD P 0)) (κ ω : ℝ) (h : Thm41Hyp P ν x0 y0 D0 κ ω) (k : ℕ) :
    projTo P k '' ball0 P ν x0 y0 κ ω ⊆ Dset P D0 k := by
  rw [Dset_eq_image]
  exact Set.image_mono h.h41e

end RealTimeIter.Contract.RTIFresh
end

-- RTIProof.RunDisplacement

noncomputable section
namespace RealTimeIter.Contract.RTIFresh
variable {P : OCP} (ν : CompatNorms P) (x0 : Vec P.nx) (y0 : PD P 0)

theorem rti_iterate_succ (k : ℕ) :
    (rti P x0 y0 (k + 1)).2 = proj P k ((rti P x0 y0 k).2 + rtiStep P x0 y0 k) := rfl

theorem rti_displacement_step (k : ℕ) :
    ν.nrm (k + 1) ((rti P x0 y0 (k + 1)).2 - projTo P (k + 1) y0) ≤
      ν.nrm k ((rti P x0 y0 k).2 - projTo P k y0) + ν.nrm k (rtiStep P x0 y0 k) := by
  rw [rti_iterate_succ, projTo_succ, ← map_sub]
  apply (ν.proj_le k _).trans
  have he : (rti P x0 y0 k).2 + rtiStep P x0 y0 k - projTo P k y0 =
      ((rti P x0 y0 k).2 - projTo P k y0) + rtiStep P x0 y0 k := by abel
  rw [he]
  exact ν.triangle k _ _

theorem rti_displacement_sum (k : ℕ) :
    ν.nrm k ((rti P x0 y0 k).2 - projTo P k y0) ≤
      ∑ i ∈ Finset.range k, ν.nrm i (rtiStep P x0 y0 i) := by
  induction k with
  | zero => simp [rti, supplied_zero]
  | succ k ih =>
    rw [Finset.sum_range_succ]
    exact (rti_displacement_step ν x0 y0 k).trans (add_le_add ih le_rfl)

end RealTimeIter.Contract.RTIFresh
end

-- RTIProof.ContractionScalars

namespace RealTimeIter.Contract.RTIFresh

theorem contraction_scalar_step {κ ω a b a0 : ℝ}
    (hω : 0 ≤ ω) (ha : 0 ≤ a)
    (ha0 : a ≤ a0) (hδ : κ + ω / 2 * a0 < 1)
    (hstep : b ≤ (κ + ω / 2 * a) * a) :
    b ≤ a ∧ κ + ω / 2 * b ≤ κ + ω / 2 * a ∧
      b ≤ (κ + ω / 2 * a0) * a := by
  have hfac : κ + ω / 2 * a ≤ κ + ω / 2 * a0 := by nlinarith
  have hba : b ≤ a := by nlinarith
  exact ⟨hba, by nlinarith, hstep.trans (mul_le_mul_of_nonneg_right hfac ha)⟩

theorem contraction_sequence_bound (a : ℕ → ℝ) (κ ω : ℝ)
    (hκ : 0 ≤ κ) (hω : 0 ≤ ω) (ha : ∀ i, 0 ≤ a i)
    (hδ : κ + ω / 2 * a 0 < 1)
    (hstep : ∀ i, a (i + 1) ≤ (κ + ω / 2 * a i) * a i) :
    ∀ i, a i ≤ (κ + ω / 2 * a 0) ^ i * a 0 ∧ a i ≤ a 0 := by
  have hd0 : 0 ≤ κ + ω / 2 * a 0 := add_nonneg hκ (mul_nonneg (div_nonneg hω (by norm_num)) (ha 0))
  intro i
  induction i with
  | zero => simp
  | succ i ih =>
    have hs := contraction_scalar_step hω (ha i) ih.2 hδ (hstep i)
    constructor
    · calc
        a (i + 1) ≤ (κ + ω / 2 * a 0) * a i := hs.2.2
        _ ≤ (κ + ω / 2 * a 0) * ((κ + ω / 2 * a 0) ^ i * a 0) :=
          mul_le_mul_of_nonneg_left ih.1 hd0
        _ = (κ + ω / 2 * a 0) ^ (i + 1) * a 0 := by rw [pow_succ]; ring
    · exact hs.1.trans ih.2

theorem geometric_budget {δ a : ℝ} (hδ : δ < 1) (k : ℕ) :
    a * (∑ i ∈ Finset.range k, δ ^ i) + δ ^ k * a / (1 - δ) = a / (1 - δ) := by
  have hd : 1 - δ ≠ 0 := by linarith
  have hs := congrArg (fun x : ℝ => a * x) (geom_sum_mul δ k)
  field_simp [hd]
  nlinarith

end RealTimeIter.Contract.RTIFresh

-- RTIProof.RunBallControl

noncomputable section
namespace RealTimeIter.Contract.RTIFresh

theorem rti_positive_control {P : OCP} (ν : CompatNorms P) (x0 : Vec P.nx)
    (y0 : PD P 0) (κ ω : ℝ) (hκ : 0 ≤ κ) (hω : 0 ≤ ω)
    (hq : delta P ν x0 y0 κ ω 0 < 1)
    (hlocal : ∀ k < P.N,
      (rti P x0 y0 k).2 ∈ projTo P k '' ball0 P ν x0 y0 κ ω →
      (rti P x0 y0 k).2 + rtiStep P x0 y0 k ∈ projTo P k '' ball0 P ν x0 y0 κ ω →
      ν.nrm (k + 1) (rtiStep P x0 y0 (k + 1)) ≤
        delta P ν x0 y0 κ ω k * ν.nrm k (rtiStep P x0 y0 k)) :
    ∀ k ≤ P.N,
      ν.nrm k (rtiStep P x0 y0 k) ≤
        delta P ν x0 y0 κ ω 0 ^ k * ν.nrm 0 (rtiStep P x0 y0 0) ∧
      ν.nrm k ((rti P x0 y0 k).2 - projTo P k y0) ≤
        ν.nrm 0 (rtiStep P x0 y0 0) * ∑ i ∈ Finset.range k, delta P ν x0 y0 κ ω 0 ^ i := by
  let a := ν.nrm 0 (rtiStep P x0 y0 0)
  let q := delta P ν x0 y0 κ ω 0
  have ha : 0 ≤ a := supplied_nonneg ν 0 _
  have hq0 : 0 ≤ q := by
    change 0 ≤ κ + ω / 2 * a
    exact add_nonneg hκ (mul_nonneg (div_nonneg hω (by norm_num)) ha)
  have hq1 : q < 1 := hq
  have hbudget (j : ℕ) : a * (∑ i ∈ Finset.range j, q ^ i) ≤ a / (1 - q) := by
    have he := geometric_budget (a := a) hq1 j
    have hp : 0 ≤ q ^ j * a / (1 - q) := by positivity
    linarith
  have hball (j : ℕ) : projTo P j '' ball0 P ν x0 y0 κ ω =
      {z | ν.nrm j (z - projTo P j y0) ≤ a / (1 - q)} :=
    projected_closedBall ν j y0 (a / (1 - q))
  intro k
  induction k with
  | zero => intro _; simp [rti, supplied_zero]
  | succ k ih =>
    intro hk
    obtain ⟨hstep, hdist⟩ := ih (by omega)
    have hcurrent : (rti P x0 y0 k).2 ∈ projTo P k '' ball0 P ν x0 y0 κ ω := by
      rw [hball]
      exact hdist.trans (hbudget k)
    have hcorrected : ν.nrm k ((rti P x0 y0 k).2 + rtiStep P x0 y0 k - projTo P k y0) ≤
        a * ∑ i ∈ Finset.range (k + 1), q ^ i := by
      have he : (rti P x0 y0 k).2 + rtiStep P x0 y0 k - projTo P k y0 =
          ((rti P x0 y0 k).2 - projTo P k y0) + rtiStep P x0 y0 k := by abel
      rw [he, Finset.sum_range_succ]
      exact (ν.triangle k _ _).trans ((add_le_add hdist hstep).trans_eq (by ring))
    have hnextball : (rti P x0 y0 k).2 + rtiStep P x0 y0 k ∈
        projTo P k '' ball0 P ν x0 y0 κ ω := by
      rw [hball]
      exact hcorrected.trans (hbudget (k + 1))
    have hs := hlocal k (by omega) hcurrent hnextball
    have hak : ν.nrm k (rtiStep P x0 y0 k) ≤ a := hstep.trans
      (by simpa using mul_le_mul_of_nonneg_right (pow_le_one₀ hq0 hq1.le) ha)
    have hc := contraction_scalar_step hω (supplied_nonneg ν k _) hak hq1 hs
    constructor
    · calc
        ν.nrm (k + 1) (rtiStep P x0 y0 (k + 1)) ≤ q * ν.nrm k (rtiStep P x0 y0 k) := hc.2.2
        _ ≤ q * (q ^ k * a) := mul_le_mul_of_nonneg_left hstep hq0
        _ = q ^ (k + 1) * a := by rw [pow_succ]; ring
    · rw [rti_iterate_succ, projTo_succ, ← map_sub]
      exact (ν.proj_le k _).trans hcorrected

end RealTimeIter.Contract.RTIFresh
end

-- RTIProof.RunBallConsequences

noncomputable section
namespace RealTimeIter.Contract.RTIFresh

theorem rti_ball_consequences {P : OCP} (ν : CompatNorms P) (x0 : Vec P.nx)
    (y0 : PD P 0) (κ ω : ℝ) (hκ : 0 ≤ κ) (hω : 0 ≤ ω)
    (hq : delta P ν x0 y0 κ ω 0 < 1) (k : ℕ)
    (hstep : ν.nrm k (rtiStep P x0 y0 k) ≤
      delta P ν x0 y0 κ ω 0 ^ k * ν.nrm 0 (rtiStep P x0 y0 0))
    (hdist : ν.nrm k ((rti P x0 y0 k).2 - projTo P k y0) ≤
      ν.nrm 0 (rtiStep P x0 y0 0) * ∑ i ∈ Finset.range k, delta P ν x0 y0 κ ω 0 ^ i) :
    (rti P x0 y0 k).2 ∈ projTo P k '' ball0 P ν x0 y0 κ ω ∧
    delta P ν x0 y0 κ ω k ≤ delta P ν x0 y0 κ ω 0 ∧
    ν.nrm k (rtiStep P x0 y0 k) / (1 - delta P ν x0 y0 κ ω k) ≤
      delta P ν x0 y0 κ ω 0 ^ k * ν.nrm 0 (rtiStep P x0 y0 0) /
        (1 - delta P ν x0 y0 κ ω 0) ∧
    {z | ν.nrm k (z - (rti P x0 y0 k).2) ≤
      ν.nrm k (rtiStep P x0 y0 k) / (1 - delta P ν x0 y0 κ ω k)} ⊆
        projTo P k '' ball0 P ν x0 y0 κ ω := by
  let a := ν.nrm 0 (rtiStep P x0 y0 0)
  let q := delta P ν x0 y0 κ ω 0
  have ha : 0 ≤ a := supplied_nonneg ν 0 _
  have hak : 0 ≤ ν.nrm k (rtiStep P x0 y0 k) := supplied_nonneg ν k _
  have hq0 : 0 ≤ q := add_nonneg hκ (mul_nonneg (div_nonneg hω (by norm_num)) ha)
  have hq1 : q < 1 := hq
  have ha0 : ν.nrm k (rtiStep P x0 y0 k) ≤ a := hstep.trans
    (by simpa using mul_le_mul_of_nonneg_right (pow_le_one₀ hq0 hq1.le) ha)
  have hd : delta P ν x0 y0 κ ω k ≤ q := by
    change κ + ω / 2 * ν.nrm k (rtiStep P x0 y0 k) ≤ κ + ω / 2 * a
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_left ha0 (div_nonneg hω (by norm_num)))
  have hden : 0 < 1 - q := sub_pos.mpr hq1
  have hr : ν.nrm k (rtiStep P x0 y0 k) / (1 - delta P ν x0 y0 κ ω k) ≤
      q ^ k * a / (1 - q) := by
    calc
      _ ≤ ν.nrm k (rtiStep P x0 y0 k) / (1 - q) :=
        div_le_div_of_nonneg_left hak hden (by linarith)
      _ ≤ _ := div_le_div_of_nonneg_right hstep hden.le
  have hbudget := geometric_budget (a := a) hq1 k
  have htail : 0 ≤ q ^ k * a / (1 - q) := by positivity
  have hball : projTo P k '' ball0 P ν x0 y0 κ ω =
      {z | ν.nrm k (z - projTo P k y0) ≤ a / (1 - q)} :=
    projected_closedBall ν k y0 (a / (1 - q))
  refine ⟨?_, hd, hr, ?_⟩
  · rw [hball]
    exact hdist.trans (by linarith)
  · intro z hz
    rw [hball]
    change ν.nrm k (z - projTo P k y0) ≤ a / (1 - q)
    have he : z - projTo P k y0 =
        (z - (rti P x0 y0 k).2) + ((rti P x0 y0 k).2 - projTo P k y0) := by abel
    rw [he]
    have hh := ν.triangle k (z - (rti P x0 y0 k).2) ((rti P x0 y0 k).2 - projTo P k y0)
    have hz' := hz.trans hr
    linarith

end RealTimeIter.Contract.RTIFresh
end

-- RTIProof.SuppliedTopology

noncomputable section
namespace RealTimeIter.Contract.RTIFresh
variable {P : OCP} (ν : CompatNorms P) (k : ℕ)

theorem supplied_coercive : ∃ c : ℝ, 0 < c ∧ ∀ x : PD P k, c * ‖x‖ ≤ ν.nrm k x := by
  classical
  by_cases hz : ∀ x : PD P k, x = 0
  · refine ⟨1, zero_lt_one, ?_⟩
    intro x
    simp [hz x, supplied_zero]
  push Not at hz
  obtain ⟨x, hx⟩ := hz
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hne : (Metric.sphere (0 : PD P k) 1).Nonempty := by
    refine ⟨‖x‖⁻¹ • x, ?_⟩
    simp [norm_smul, ne_of_gt hn]
  obtain ⟨z, hz, hmin⟩ := (isCompact_sphere (0 : PD P k) 1).exists_isMinOn
    hne (supplied_continuous ν k).continuousOn
  have hz0 : z ≠ 0 := by intro he; simp [he] at hz
  refine ⟨ν.nrm k z, supplied_pos ν k hz0, ?_⟩
  intro y
  by_cases hy : y = 0
  · simp [hy, supplied_zero]
  have hn : 0 < ‖y‖ := norm_pos_iff.mpr hy
  have hym : ‖y‖⁻¹ • y ∈ Metric.sphere (0 : PD P k) 1 := by
    simp [norm_smul, ne_of_gt hn]
  have hi := hmin hym
  change ν.nrm k z ≤ ν.nrm k (‖y‖⁻¹ • y) at hi
  rw [ν.smul, abs_of_pos (inv_pos.mpr hn)] at hi
  calc
    ν.nrm k z * ‖y‖ ≤ (‖y‖⁻¹ * ν.nrm k y) * ‖y‖ :=
      mul_le_mul_of_nonneg_right hi hn.le
    _ = ν.nrm k y := by field_simp

theorem supplied_ball_compact (z : PD P k) (R : ℝ) :
    IsCompact {x : PD P k | ν.nrm k (x - z) ≤ R} := by
  obtain ⟨c, hc, hb⟩ := supplied_coercive ν k
  apply (isCompact_closedBall z (R / c)).of_isClosed_subset
    (isClosed_le ((supplied_continuous ν k).comp (continuous_id.sub continuous_const))
      continuous_const)
  intro x hx
  rw [Metric.mem_closedBall, dist_eq_norm, le_div_iff₀ hc]
  exact (mul_comm ‖x - z‖ c).le.trans ((hb (x - z)).trans hx)

theorem supplied_ball_convex (z : PD P k) (R : ℝ) :
    Convex ℝ {x : PD P k | ν.nrm k (x - z) ≤ R} := by
  intro x hx y hy a b ha hb hab
  change ν.nrm k (a • x + b • y - z) ≤ R
  have he : a • (x - z) + b • (y - z) = a • x + b • y - (a + b) • z := by module
  rw [hab, one_smul] at he
  rw [← he]
  have ht := ν.triangle k (a • (x - z)) (b • (y - z))
  rw [ν.smul, ν.smul, abs_of_nonneg ha, abs_of_nonneg hb] at ht
  have hx' := mul_le_mul_of_nonneg_left hx ha
  have hy' := mul_le_mul_of_nonneg_left hy hb
  exact ht.trans ((add_le_add hx' hy').trans_eq (by rw [← add_mul, hab, one_mul]))

end RealTimeIter.Contract.RTIFresh
end

-- RTIProof.GeometricConvergence

noncomputable section
namespace RealTimeIter.Contract.RTIFresh
open Filter Topology

theorem supplied_geometric_cauchy {P : OCP} (ν : CompatNorms P) (k : ℕ)
    (z : ℕ → PD P k) (a q : ℝ) (hq : q < 1)
    (hz : ∀ i, ν.nrm k (z (i + 1) - z i) ≤ q ^ i * a) : CauchySeq z := by
  obtain ⟨c, hc, hb⟩ := supplied_coercive ν k
  apply cauchySeq_of_le_geometric q (a / c) hq
  intro i
  rw [dist_comm, dist_eq_norm]
  have hi := (hb (z (i + 1) - z i)).trans (hz i)
  calc
    ‖z (i + 1) - z i‖ ≤ (q ^ i * a) / c :=
      (le_div_iff₀ hc).mpr (by simpa only [mul_comm] using hi)
    _ = a / c * q ^ i := by ring

theorem supplied_geometric_prefix {P : OCP} (ν : CompatNorms P) (k : ℕ)
    (z : ℕ → PD P k) (a q : ℝ)
    (hz : ∀ i, ν.nrm k (z (i + 1) - z i) ≤ q ^ i * a) :
    ∀ j, ν.nrm k (z j - z 0) ≤ a * ∑ i ∈ Finset.range j, q ^ i := by
  intro j
  induction j with
  | zero => simp [supplied_zero]
  | succ j ih =>
    have he : z (j + 1) - z 0 = (z (j + 1) - z j) + (z j - z 0) := by abel
    rw [he, Finset.sum_range_succ]
    calc
      ν.nrm k ((z (j + 1) - z j) + (z j - z 0)) ≤
          ν.nrm k (z (j + 1) - z j) + ν.nrm k (z j - z 0) := ν.triangle k _ _
      _ ≤ q ^ j * a + a * ∑ i ∈ Finset.range j, q ^ i := add_le_add (hz j) ih
      _ = a * ((∑ i ∈ Finset.range j, q ^ i) + q ^ j) := by ring

theorem supplied_geometric_limit {P : OCP} (ν : CompatNorms P) (k : ℕ)
    (z : ℕ → PD P k) (a q : ℝ) (ha : 0 ≤ a) (hq0 : 0 ≤ q) (hq : q < 1)
    (hz : ∀ i, ν.nrm k (z (i + 1) - z i) ≤ q ^ i * a) :
    ∃ l, Tendsto z atTop (𝓝 l) ∧ ν.nrm k (z 0 - l) ≤ a / (1 - q) := by
  obtain ⟨l, hl⟩ := cauchySeq_tendsto_of_complete (supplied_geometric_cauchy ν k z a q hq hz)
  refine ⟨l, hl, ?_⟩
  have hbound : ∀ j, ν.nrm k (z j - z 0) ≤ a / (1 - q) := by
    intro j
    have hg := geometric_budget (a := a) hq j
    have hp : 0 ≤ q ^ j * a / (1 - q) := by positivity
    exact (supplied_geometric_prefix ν k z a q hz j).trans (by linarith)
  have ht := ((supplied_continuous ν k).tendsto (l - z 0)).comp
    (hl.sub tendsto_const_nhds)
  have hb := le_of_tendsto ht (Filter.Eventually.of_forall hbound)
  rw [supplied_sub_rev] at hb
  exact hb

end RealTimeIter.Contract.RTIFresh
end

-- RTIProof.LocalNewtonControl

noncomputable section
namespace RealTimeIter.Contract.RTIFresh

theorem local_newton_control {P : OCP} (ν : CompatNorms P) (k : ℕ)
    (F : PD P k → PD P k) (z : ℕ → PD P k) (κ ω : ℝ)
    (hκ : 0 ≤ κ) (hω : 0 ≤ ω)
    (hz : ∀ i, z (i + 1) = z i + F (z i))
    (hq : κ + ω / 2 * ν.nrm k (F (z 0)) < 1)
    (hlocal : ∀ y,
      ν.nrm k (y - z 0) ≤ ν.nrm k (F (z 0)) / (1 - (κ + ω / 2 * ν.nrm k (F (z 0)))) →
      ν.nrm k (y + F y - z 0) ≤ ν.nrm k (F (z 0)) / (1 - (κ + ω / 2 * ν.nrm k (F (z 0)))) →
      ν.nrm k (F (y + F y)) ≤ (κ + ω / 2 * ν.nrm k (F y)) * ν.nrm k (F y)) :
    ∀ i,
      ν.nrm k (F (z i)) ≤ (κ + ω / 2 * ν.nrm k (F (z 0))) ^ i * ν.nrm k (F (z 0)) ∧
      ν.nrm k (z i - z 0) ≤ ν.nrm k (F (z 0)) *
        ∑ j ∈ Finset.range i, (κ + ω / 2 * ν.nrm k (F (z 0))) ^ j := by
  let a := ν.nrm k (F (z 0))
  let q := κ + ω / 2 * a
  have ha : 0 ≤ a := supplied_nonneg ν k _
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hq1 : q < 1 := hq
  have hprefix (j : ℕ) : a * (∑ l ∈ Finset.range j, q ^ l) ≤ a / (1 - q) := by
    have h := geometric_budget (a := a) hq1 j
    have ht : 0 ≤ q ^ j * a / (1 - q) := by positivity
    linarith
  intro i
  change ν.nrm k (F (z i)) ≤ q ^ i * a ∧
    ν.nrm k (z i - z 0) ≤ a * ∑ j ∈ Finset.range i, q ^ j
  induction i with
  | zero => simp [a, supplied_zero]
  | succ i ih =>
    have hnext : ν.nrm k (z (i + 1) - z 0) ≤ a * ∑ j ∈ Finset.range (i + 1), q ^ j := by
      rw [hz i]
      have he : z i + F (z i) - z 0 = F (z i) + (z i - z 0) := by abel
      rw [he, Finset.sum_range_succ]
      exact (ν.triangle k _ _).trans ((add_le_add ih.1 ih.2).trans_eq (by ring))
    have hstep := hlocal (z i) (ih.2.trans (hprefix i))
      (by rw [← hz i]; exact hnext.trans (hprefix (i + 1)))
    rw [← hz i] at hstep
    have hai : ν.nrm k (F (z i)) ≤ a := ih.1.trans
      (by simpa using mul_le_mul_of_nonneg_right (pow_le_one₀ hq0 hq1.le) ha)
    have hs := contraction_scalar_step hω (supplied_nonneg ν k _) hai hq1 hstep
    refine ⟨?_, hnext⟩
    calc
      ν.nrm k (F (z (i + 1))) ≤ q * ν.nrm k (F (z i)) := hs.2.2
      _ ≤ q * (q ^ i * a) := mul_le_mul_of_nonneg_left ih.1 hq0
      _ = q ^ (i + 1) * a := by rw [pow_succ]; ring

end RealTimeIter.Contract.RTIFresh
end

-- RTIProof.StationaryLimit

noncomputable section
namespace RealTimeIter.Contract.RTIFresh
open Filter Topology

theorem stationary_limit_of_steps {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F g : E → E) (J : E → E →L[ℝ] E) (D : Set E) (z : ℕ → E) (l : E)
    (hz : ∀ i, z (i + 1) = z i + F (z i))
    (hmem : ∀ i, z i ∈ D) (hlmem : l ∈ D) (hl : Tendsto z atTop (𝓝 l))
    (hJ : ContinuousOn J D) (hg : ContinuousOn g D)
    (hres : ∀ y ∈ D, g y = -(J y) (F y)) : g l = 0 := by
  have hwithin : Tendsto z atTop (𝓝[D] l) :=
    tendsto_nhdsWithin_iff.mpr ⟨hl, Eventually.of_forall hmem⟩
  have hJl : Tendsto (fun i => J (z i)) atTop (𝓝 (J l)) := (show Tendsto J (𝓝[D] l) (𝓝 (J l)) from hJ l hlmem).comp hwithin
  have hgl : Tendsto (fun i => g (z i)) atTop (𝓝 (g l)) := (show Tendsto g (𝓝[D] l) (𝓝 (g l)) from hg l hlmem).comp hwithin
  have hdiff := (hl.comp (tendsto_add_atTop_nat 1)).sub hl
  have hF : Tendsto (fun i => F (z i)) atTop (𝓝 (0 : E)) := by
    have he : (fun i => z (i + 1) - z i) = fun i => F (z i) := by
      funext i
      rw [hz i, add_sub_cancel_left]
    simpa only [Function.comp_def, sub_self, he] using hdiff
  have happ : Continuous (fun p : (E →L[ℝ] E) × E => p.1 p.2) := by fun_prop
  have ht := happ.continuousAt.tendsto.comp (hJl.prodMk_nhds hF)
  have hzero : Tendsto (fun i => g (z i)) atTop (𝓝 (0 : E)) := by
    have he : (fun i => g (z i)) = fun i => -(J (z i)) (F (z i)) := by
      funext i
      exact hres (z i) (hmem i)
    rw [he]
    simpa only [Function.comp_def, map_zero, neg_zero] using ht.neg
  exact tendsto_nhds_unique hgl hzero

end RealTimeIter.Contract.RTIFresh
end

-- RTIProof.LocalNewtonLimit

noncomputable section
namespace RealTimeIter.Contract.RTIFresh
open Filter Topology

theorem local_newton_limit {P : OCP} (ν : CompatNorms P) (k : ℕ)
    (F g : PD P k → PD P k) (J : PD P k → PD P k →L[ℝ] PD P k)
    (z : ℕ → PD P k) (κ ω : ℝ) (hκ : 0 ≤ κ) (hω : 0 ≤ ω)
    (hz : ∀ i, z (i + 1) = z i + F (z i))
    (hq : κ + ω / 2 * ν.nrm k (F (z 0)) < 1)
    (hlocal : ∀ y,
      ν.nrm k (y - z 0) ≤ ν.nrm k (F (z 0)) / (1 - (κ + ω / 2 * ν.nrm k (F (z 0)))) →
      ν.nrm k (y + F y - z 0) ≤ ν.nrm k (F (z 0)) / (1 - (κ + ω / 2 * ν.nrm k (F (z 0)))) →
      ν.nrm k (F (y + F y)) ≤ (κ + ω / 2 * ν.nrm k (F y)) * ν.nrm k (F y))
    (hJ : ContinuousOn J {y | ν.nrm k (y - z 0) ≤
      ν.nrm k (F (z 0)) / (1 - (κ + ω / 2 * ν.nrm k (F (z 0))))})
    (hg : ContinuousOn g {y | ν.nrm k (y - z 0) ≤
      ν.nrm k (F (z 0)) / (1 - (κ + ω / 2 * ν.nrm k (F (z 0))))})
    (hres : ∀ y, ν.nrm k (y - z 0) ≤
      ν.nrm k (F (z 0)) / (1 - (κ + ω / 2 * ν.nrm k (F (z 0)))) →
      g y = -(J y) (F y)) :
    ∃ l, Tendsto z atTop (𝓝 l) ∧ g l = 0 ∧
      ν.nrm k (z 0 - l) ≤ ν.nrm k (F (z 0)) /
        (1 - (κ + ω / 2 * ν.nrm k (F (z 0)))) := by
  let a := ν.nrm k (F (z 0))
  let q := κ + ω / 2 * a
  have ha : 0 ≤ a := supplied_nonneg ν k _
  have hq0 : 0 ≤ q := add_nonneg hκ (mul_nonneg (div_nonneg hω (by norm_num)) ha)
  have hc := local_newton_control ν k F z κ ω hκ hω hz hq hlocal
  have hinc : ∀ i, ν.nrm k (z (i + 1) - z i) ≤ q ^ i * a := by
    intro i
    rw [hz i, add_sub_cancel_left]
    exact (hc i).1
  obtain ⟨l, hl, hdist⟩ := supplied_geometric_limit ν k z a q ha hq0 hq hinc
  have hmem : ∀ i, ν.nrm k (z i - z 0) ≤ a / (1 - q) := by
    intro i
    have hb := geometric_budget (a := a) hq i
    have hp : 0 ≤ q ^ i * a / (1 - q) := by positivity
    exact (hc i).2.trans (by linarith)
  have hlmem : ν.nrm k (l - z 0) ≤ a / (1 - q) := by
    rw [supplied_sub_rev]
    exact hdist
  refine ⟨l, hl, ?_, hdist⟩
  exact stationary_limit_of_steps F g J {y | ν.nrm k (y - z 0) ≤ a / (1 - q)}
    z l hz hmem hlmem hl hJ hg hres

end RealTimeIter.Contract.RTIFresh
end

-- RTIProof.NewtonIterationBasics

noncomputable section
namespace RealTimeIter.Contract.RTIFresh
open Filter Topology

theorem newton_iter_zero (P : OCP) (k : ℕ) (x : Vec P.nx) (y : PD P k) :
    newtonIter P k x y 0 = y := rfl

theorem newton_iter_succ (P : OCP) (k : ℕ) (x : Vec P.nx) (y : PD P k) (i : ℕ) :
    newtonIter P k x y (i + 1) = newtonIter P k x y i + step P k x (newtonIter P k x y i) := rfl

theorem newton_constant_of_step_zero (P : OCP) (k : ℕ) (x : Vec P.nx) (y : PD P k)
    (hy : step P k x y = 0) : ∀ i, newtonIter P k x y i = y := by
  intro i
  induction i with
  | zero => rfl
  | succ i ih => rw [newton_iter_succ, ih, hy, add_zero]

theorem newton_tendsto_of_step_zero (P : OCP) (k : ℕ) (x : Vec P.nx) (y : PD P k)
    (hy : step P k x y = 0) : Tendsto (newtonIter P k x y) atTop (𝓝 y) := by
  have he : newtonIter P k x y = fun _ => y := funext (newton_constant_of_step_zero P k x y hy)
  rw [he]
  exact tendsto_const_nhds

theorem rti_zero_iterates (P : OCP) (x0 : Vec P.nx) (y0 : PD P 0)
    (hz : ∀ k ≤ P.N, rtiStep P x0 y0 k = 0) :
    ∀ k ≤ P.N, (rti P x0 y0 k).2 = projTo P k y0 := by
  intro k
  induction k with
  | zero => intro _; simp [rti]
  | succ k ih =>
    intro hk
    rw [rti_iterate_succ, hz k (by omega), add_zero, ih (by omega), ← projTo_succ]

end RealTimeIter.Contract.RTIFresh
end

-- RTIProof.AccessorCoordinates

noncomputable section
namespace RealTimeIter.Contract.RTIFresh

 theorem lamL_apply (P : OCP) (k i : ℕ) (y : PD P k) (j : Fin P.nx) :
    lamL P k i y j = if h : i < P.N + 1 ∧ k ≤ i then
      y ⟨Sum.inl (⟨i, h.1⟩, j), h.2⟩ else 0 := by
  unfold lamL
  rw [pull_apply]
  split_ifs <;> rfl

 theorem sL_apply (P : OCP) (k i : ℕ) (y : PD P k) (j : Fin P.nx) :
    sL P k i y j = if h : i < P.N + 1 ∧ k ≤ i then
      y ⟨Sum.inr (Sum.inl (⟨i, h.1⟩, j)), h.2⟩ else 0 := by
  unfold sL
  rw [pull_apply]
  split_ifs <;> rfl

 theorem qL_apply (P : OCP) (k i : ℕ) (y : PD P k) (j : Fin P.nu) :
    qL P k i y j = if h : i < P.N ∧ k ≤ i then
      y ⟨Sum.inr (Sum.inr (⟨i, h.1⟩, j)), h.2⟩ else 0 := by
  unfold qL
  rw [pull_apply]
  split_ifs <;> rfl

 theorem lamL_proj (P : OCP) (k i : ℕ) (hi : k + 1 ≤ i) (y : PD P k) :
    lamL P (k + 1) i (proj P k y) = lamL P k i y := by
  ext j
  simp only [lamL_apply, proj_apply]
  split_ifs <;> first | rfl | omega

 theorem sL_proj (P : OCP) (k i : ℕ) (hi : k + 1 ≤ i) (y : PD P k) :
    sL P (k + 1) i (proj P k y) = sL P k i y := by
  ext j
  simp only [sL_apply, proj_apply]
  split_ifs <;> first | rfl | omega

 theorem qL_proj (P : OCP) (k i : ℕ) (hi : k + 1 ≤ i) (y : PD P k) :
    qL P (k + 1) i (proj P k y) = qL P k i y := by
  ext j
  simp only [qL_apply, proj_apply]
  split_ifs <;> first | rfl | omega

 theorem projT_ofLp (P : OCP) (k : ℕ) (z : PD P (k + 1))
    (c : {c : Coord P // k ≤ stage c}) :
    (projT P k z).ofLp c = if h : k + 1 ≤ stage c.val then
      z.ofLp ⟨c.val, h⟩ else 0 := projT_apply P k z c

 theorem lamL_projT (P : OCP) (k i : ℕ) (z : PD P (k + 1)) :
    lamL P k i (projT P k z) = lamL P (k + 1) i z := by
  ext j
  by_cases hb : i < P.N + 1
  · by_cases hn : k + 1 ≤ i
    · have ho : k ≤ i := by omega
      simp only [lamL_apply, dif_pos (And.intro hb ho), dif_pos (And.intro hb hn)]
      rw [projT_ofLp]
      exact dif_pos hn
    · by_cases ho : k ≤ i
      · simp only [lamL_apply, dif_pos (And.intro hb ho), dif_neg (show ¬(i < P.N + 1 ∧ k + 1 ≤ i) by omega)]
        rw [projT_ofLp]
        exact dif_neg hn
      · simp [lamL_apply, ho, hn]
  · simp [lamL_apply, hb]

 theorem sL_projT (P : OCP) (k i : ℕ) (z : PD P (k + 1)) :
    sL P k i (projT P k z) = sL P (k + 1) i z := by
  ext j
  by_cases hb : i < P.N + 1
  · by_cases hn : k + 1 ≤ i
    · have ho : k ≤ i := by omega
      simp only [sL_apply, dif_pos (And.intro hb ho), dif_pos (And.intro hb hn)]
      rw [projT_ofLp]
      exact dif_pos hn
    · by_cases ho : k ≤ i
      · simp only [sL_apply, dif_pos (And.intro hb ho), dif_neg (show ¬(i < P.N + 1 ∧ k + 1 ≤ i) by omega)]
        rw [projT_ofLp]
        exact dif_neg hn
      · simp [sL_apply, ho, hn]
  · simp [sL_apply, hb]

 theorem qL_projT (P : OCP) (k i : ℕ) (z : PD P (k + 1)) :
    qL P k i (projT P k z) = qL P (k + 1) i z := by
  ext j
  by_cases hb : i < P.N
  · by_cases hn : k + 1 ≤ i
    · have ho : k ≤ i := by omega
      simp only [qL_apply, dif_pos (And.intro hb ho), dif_pos (And.intro hb hn)]
      rw [projT_ofLp]
      exact dif_pos hn
    · by_cases ho : k ≤ i
      · simp only [qL_apply, dif_pos (And.intro hb ho), dif_neg (show ¬(i < P.N ∧ k + 1 ≤ i) by omega)]
        rw [projT_ofLp]
        exact dif_neg hn
      · simp [qL_apply, ho, hn]
  · simp [qL_apply, hb]

@[simp] theorem lamL_projT_current (P : OCP) (k : ℕ) (z : PD P (k + 1)) :
    lamL P k k (projT P k z) = 0 := by
  rw [lamL_projT]
  ext j
  simp [lamL_apply]

@[simp] theorem sL_projT_current (P : OCP) (k : ℕ) (z : PD P (k + 1)) :
    sL P k k (projT P k z) = 0 := by
  rw [sL_projT]
  ext j
  simp [sL_apply]

@[simp] theorem qL_projT_current (P : OCP) (k : ℕ) (z : PD P (k + 1)) :
    qL P k k (projT P k z) = 0 := by
  rw [qL_projT]
  ext j
  simp [qL_apply]

end RealTimeIter.Contract.RTIFresh
end

-- RTIProof.LagrangianRestriction

noncomputable section
namespace RealTimeIter.Contract.RTIFresh
open scoped InnerProductSpace

 theorem lagr_initial_shift (P : OCP) (k : ℕ) (x : Vec P.nx) (y : PD P k) :
    lagr P k x y = lagr P k 0 y + ⟪lamL P k k y, x⟫_ℝ := by
  simp only [lagr, inner_sub_right, inner_zero_right]
  ring

 theorem lagr_split (P : OCP) (k : ℕ) (hk : k < P.N)
    (x : Vec P.nx) (y : PD P k) :
    lagr P k x y = P.L k (sL P k k y) (qL P k k y) +
      ⟪lamL P k k y, x - sL P k k y⟫_ℝ +
      lagr P (k + 1) (P.f k (sL P k k y) (qL P k k y)) (proj P k y) := by
  have hc : (∑ i ∈ Finset.Ico (k + 1) P.N,
      P.L i (sL P (k + 1) i (proj P k y)) (qL P (k + 1) i (proj P k y))) =
      ∑ i ∈ Finset.Ico (k + 1) P.N, P.L i (sL P k i y) (qL P k i y) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [sL_proj P k i (Finset.mem_Ico.mp hi).1,
      qL_proj P k i (Finset.mem_Ico.mp hi).1]
  have hf : (∑ i ∈ Finset.Ico (k + 1) P.N,
      ⟪lamL P (k + 1) (i + 1) (proj P k y),
        P.f i (sL P (k + 1) i (proj P k y)) (qL P (k + 1) i (proj P k y)) -
          sL P (k + 1) (i + 1) (proj P k y)⟫_ℝ) =
      ∑ i ∈ Finset.Ico (k + 1) P.N,
        ⟪lamL P k (i + 1) y, P.f i (sL P k i y) (qL P k i y) -
          sL P k (i + 1) y⟫_ℝ := by
    apply Finset.sum_congr rfl
    intro i hi
    have hki := (Finset.mem_Ico.mp hi).1
    rw [lamL_proj P k (i + 1) (by omega), sL_proj P k i hki,
      qL_proj P k i hki, sL_proj P k (i + 1) (by omega)]
  simp only [lagr]
  rw [hc, hf, sL_proj P k P.N (by omega), lamL_proj P k (k + 1) le_rfl,
    sL_proj P k (k + 1) le_rfl,
    Finset.sum_eq_sum_Ico_succ_bot hk, Finset.sum_eq_sum_Ico_succ_bot hk]
  ring

 theorem lagr_affine_restriction (P : OCP) (k : ℕ) (hk : k < P.N)
    (x : Vec P.nx) (y : PD P k) (z : PD P (k + 1)) :
    lagr P k x (y + projT P k z) =
      lagr P (k + 1) (P.f k (sL P k k y) (qL P k k y)) (proj P k y + z) +
      (P.L k (sL P k k y) (qL P k k y) + ⟪lamL P k k y, x - sL P k k y⟫_ℝ) := by
  rw [lagr_split P k hk]
  simp only [map_add, sL_projT_current, qL_projT_current, lamL_projT_current,
    add_zero, proj_projT]
  ring

end RealTimeIter.Contract.RTIFresh
end

-- RTIProof.AffineGradient

noncomputable section
namespace RealTimeIter.Contract.RTIFresh
open scoped InnerProductSpace
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

theorem gradient_affine_restriction (L : F →L[ℝ] E) (R : E →L[ℝ] F)
    (hLR : ∀ a b, ⟪R a, b⟫_ℝ = ⟪a, L b⟫_ℝ)
    (f : E → ℝ) (g : F → ℝ) (y : E) (c : ℝ)
    (heq : ∀ z, f (y + L z) = g z + c) (z : F)
    (hf : DifferentiableAt ℝ f (y + L z)) (hg : DifferentiableAt ℝ g z) :
    R (gradient f (y + L z)) = gradient g z := by
  have ha := hf.hasFDerivAt.comp z ((hasFDerivAt_const y z).add L.hasFDerivAt)
  have hb := hg.hasFDerivAt.add_const c
  have hfun : (fun w => f (y + L w)) = (fun w => g w + c) := funext heq
  have hd : (fderiv ℝ f (y + L z)).comp L = fderiv ℝ g z := by
    have hh := ha
    simp only [zero_add] at hh
    change HasFDerivAt (fun w => f (y + L w)) _ z at hh
    rw [hfun] at hh
    exact hh.unique hb
  apply ext_inner_right ℝ
  intro b
  rw [hLR, inner_gradient_left, inner_gradient_left]
  exact congrArg (fun T : F →L[ℝ] ℝ => T b) hd

end RealTimeIter.Contract.RTIFresh
end

-- RTIProof.GradientRegularity

noncomputable section
namespace RealTimeIter.Contract.RTIFresh
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem gradient_contDiffAt {f : E → ℝ} {x : E} (hf : ContDiffAt ℝ 2 f x) :
    ContDiffAt ℝ 1 (gradient f) x := by
  have hd : ContDiffAt ℝ 1 (fderiv ℝ f) x := hf.fderiv_right (by norm_num)
  exact (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.contDiff.contDiffAt.comp x hd

theorem gradient_continuousAt {f : E → ℝ} {x : E} (hf : ContDiffAt ℝ 2 f x) :
    ContinuousAt (gradient f) x := (gradient_contDiffAt hf).continuousAt

theorem gradient_differentiableAt {f : E → ℝ} {x : E} (hf : ContDiffAt ℝ 2 f x) :
    DifferentiableAt ℝ (gradient f) x := (gradient_contDiffAt hf).differentiableAt (by norm_num)

end RealTimeIter.Contract.RTIFresh
end

-- RTIProof.NativeGradient

noncomputable section
namespace RealTimeIter.Contract.RTIFresh
open scoped InnerProductSpace

theorem lagr_contDiffAt_initial (P : OCP) (k : ℕ) (x : Vec P.nx) (y : PD P k)
    (hc : ContDiffAt ℝ 2 (lagr P k 0) y) : ContDiffAt ℝ 2 (lagr P k x) y := by
  have hl : ContDiff ℝ 2 (fun z : PD P k => ⟪lamL P k k z, x⟫_ℝ) :=
    (lamL P k k).contDiff.inner ℝ contDiff_const
  have heq : lagr P k x = fun z => lagr P k 0 z + ⟪lamL P k k z, x⟫_ℝ :=
    funext (lagr_initial_shift P k x)
  rw [heq]
  exact hc.add hl.contDiffAt

theorem grad_affine_restriction (P : OCP) (k : ℕ) (hk : k < P.N)
    (x : Vec P.nx) (y : PD P k) (z : PD P (k + 1))
    (hc : ContDiffAt ℝ 2 (lagr P k 0) (y + projT P k z))
    (hd : ContDiffAt ℝ 2 (lagr P (k + 1) 0) (proj P k y + z)) :
    proj P k (grad P k x (y + projT P k z)) =
      grad P (k + 1) (P.f k (sL P k k y) (qL P k k y)) (proj P k y + z) := by
  let f := lagr P k x
  let x' := P.f k (sL P k k y) (qL P k k y)
  let g := fun w => lagr P (k + 1) x' (proj P k y + w)
  have hf := (lagr_contDiffAt_initial P k x _ hc).differentiableAt (by norm_num)
  have hg0 := (lagr_contDiffAt_initial P (k + 1) x' _ hd).differentiableAt (by norm_num)
  have hg := hg0.comp z (differentiableAt_const (proj P k y) |>.add differentiableAt_id)
  have hh := gradient_affine_restriction (projT P k) (proj P k) (proj_inner_projT P k)
    f g y (P.L k (sL P k k y) (qL P k k y) + ⟪lamL P k k y, x - sL P k k y⟫_ℝ)
    (lagr_affine_restriction P k hk x y) z hf hg
  have ht := gradient_affine_restriction (ContinuousLinearMap.id ℝ (PD P (k + 1)))
    (ContinuousLinearMap.id ℝ (PD P (k + 1))) (by intros; rfl)
    (lagr P (k + 1) x') g (proj P k y) 0 (by intro w; simp [g]) z hg0 hg
  simpa only [grad, f, ContinuousLinearMap.id_apply] using hh.trans ht.symm

end RealTimeIter.Contract.RTIFresh
end

-- RTIProof.StepResidual

noncomputable section
namespace RealTimeIter.Contract.RTIFresh

theorem step_residual (P : OCP) (k : ℕ) (x : Vec P.nx) (y : PD P k)
    (hi : (J P k y).IsInvertible) : grad P k x y = -(J P k y) (step P k x y) := by
  simp only [step, map_neg, neg_neg, hi.self_apply_inverse]

theorem step_zero_iff (P : OCP) (k : ℕ) (x : Vec P.nx) (y : PD P k)
    (hi : (J P k y).IsInvertible) : step P k x y = 0 ↔ grad P k x y = 0 := by
  constructor
  · intro hz
    rw [step_residual P k x y hi, hz, map_zero, neg_zero]
  · intro hz
    simp only [step, hz, map_zero, neg_zero]

end RealTimeIter.Contract.RTIFresh
end

-- RTIProof.NativeNewtonLimit

noncomputable section
namespace RealTimeIter.Contract.RTIFresh
open Filter Topology

theorem native_newton_limit {P : OCP} (ν : CompatNorms P)
    (x0 : Vec P.nx) (y0 : PD P 0) (D0 : Set (PD P 0)) (κ ω : ℝ)
    (h : Thm41Hyp P ν x0 y0 D0 κ ω) (hκ : 0 ≤ κ) (hω : 0 ≤ ω)
    (k : ℕ) (hk : k ≤ P.N) (x : Vec P.nx) (y : PD P k)
    (hq : κ + ω / 2 * ν.nrm k (step P k x y) < 1)
    (hball : {z | ν.nrm k (z - y) ≤ ν.nrm k (step P k x y) /
      (1 - (κ + ω / 2 * ν.nrm k (step P k x y)))} ⊆ Dset P D0 k)
    (hlocal : ∀ z ∈ Dset P D0 k, z + step P k x z ∈ Dset P D0 k →
      (∀ t ∈ Set.Icc (0 : ℝ) 1, z + t • step P k x z ∈ Dset P D0 k) →
      ν.nrm k (step P k x (z + step P k x z)) ≤
        (κ + ω / 2 * ν.nrm k (step P k x z)) * ν.nrm k (step P k x z)) :
    ∃ l, Tendsto (newtonIter P k x y) atTop (𝓝 l) ∧ grad P k x l = 0 ∧
      ν.nrm k (y - l) ≤ ν.nrm k (step P k x y) /
        (1 - (κ + ω / 2 * ν.nrm k (step P k x y))) := by
  let B := {z | ν.nrm k (z - y) ≤ ν.nrm k (step P k x y) /
    (1 - (κ + ω / 2 * ν.nrm k (step P k x y)))}
  have hconv : Convex ℝ B := supplied_ball_convex ν k y _
  have hstep : ∀ z ∈ B, z + step P k x z ∈ B →
      ν.nrm k (step P k x (z + step P k x z)) ≤
        (κ + ω / 2 * ν.nrm k (step P k x z)) * ν.nrm k (step P k x z) := by
    intro z hz hz'
    apply hlocal z (hball hz) (hball hz')
    intro t ht
    apply hball
    have hm := hconv hz hz' (sub_nonneg.mpr ht.2) ht.1 (by ring : (1 - t) + t = 1)
    have he : (1 - t) • z + t • (z + step P k x z) = z + t • step P k x z := by module
    rwa [he] at hm
  have hgc : ContinuousOn (grad P k x) B := by
    intro z hz
    exact (gradient_continuousAt (lagr_contDiffAt_initial P k x z (h.c2 k hk z (hball hz)))).continuousWithinAt
  exact local_newton_limit ν k (step P k x) (grad P k x) (J P k) (newtonIter P k x y)
    κ ω hκ hω (newton_iter_succ P k x y) hq hstep ((h.J_cont k hk).mono hball) hgc
    (fun z hz => step_residual P k x z (h.J_inv k hk z (hball hz)))

end RealTimeIter.Contract.RTIFresh
end

-- RTIProof.LinearPerturbation

noncomputable section
namespace RealTimeIter.Contract.RTIFresh
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem gradient_add_linear {f : E → ℝ} (L : E →L[ℝ] ℝ) {x : E}
    (hf : DifferentiableAt ℝ f x) :
    gradient (fun y => f y + L y) x = gradient f x + (InnerProductSpace.toDual ℝ E).symm L := by
  apply ext_inner_right ℝ
  intro v
  rw [inner_add_left, inner_gradient_left, inner_gradient_left,
    InnerProductSpace.toDual_symm_apply]
  have hd := hf.hasFDerivAt.add L.hasFDerivAt
  change (fderiv ℝ (fun y => f y + L y) x) v = _
  have he : fderiv ℝ (fun y => f y + L y) x = fderiv ℝ f x + L := hd.fderiv
  rw [he]
  rfl

theorem hessian_add_linear {f : E → ℝ} (L : E →L[ℝ] ℝ) {x : E}
    (hf : ContDiffAt ℝ 2 f x) :
    fderiv ℝ (gradient (fun y => f y + L y)) x = fderiv ℝ (gradient f) x := by
  have he : gradient (fun y => f y + L y) =ᶠ[nhds x]
      (fun y => gradient f y + (InnerProductSpace.toDual ℝ E).symm L) := by
    filter_upwards [hf.eventually (by norm_num)] with y hy
    exact gradient_add_linear L (hy.differentiableAt (by norm_num))
  rw [he.fderiv_eq]
  exact ((gradient_differentiableAt hf).hasFDerivAt.add_const _).fderiv

end RealTimeIter.Contract.RTIFresh
end

-- RTIProof.NativeHessian

noncomputable section
namespace RealTimeIter.Contract.RTIFresh
open scoped InnerProductSpace

theorem grad_fderiv_initial (P : OCP) (k : ℕ) (x : Vec P.nx) (y : PD P k)
    (hc : ContDiffAt ℝ 2 (lagr P k 0) y) :
    fderiv ℝ (grad P k x) y = hess P k y := by
  let L : PD P k →L[ℝ] ℝ := (InnerProductSpace.toDual ℝ (Vec P.nx) x).comp (lamL P k k)
  have he : lagr P k x = fun z => lagr P k 0 z + L z := by
    funext z
    rw [lagr_initial_shift]
    simp only [L, ContinuousLinearMap.comp_apply, InnerProductSpace.toDual_apply_apply,
      real_inner_comm]
  change fderiv ℝ (gradient (lagr P k x)) y = fderiv ℝ (gradient (lagr P k 0)) y
  rw [he]
  exact hessian_add_linear L hc

theorem grad_hasFDerivAt (P : OCP) (k : ℕ) (x : Vec P.nx) (y : PD P k)
    (hc : ContDiffAt ℝ 2 (lagr P k 0) y) :
    HasFDerivAt (grad P k x) (hess P k y) y := by
  have hd := gradient_differentiableAt (lagr_contDiffAt_initial P k x y hc)
  rw [← grad_fderiv_initial P k x y hc]
  exact hd.hasFDerivAt

end RealTimeIter.Contract.RTIFresh
end

-- RTIProof.GradientPath

noncomputable section
namespace RealTimeIter.Contract.RTIFresh
open Set

theorem hess_continuousAt (P : OCP) (k : ℕ) (y : PD P k)
    (hc : ContDiffAt ℝ 2 (lagr P k 0) y) : ContinuousAt (hess P k) y :=
  (gradient_contDiffAt hc).continuousAt_fderiv (by norm_num)

theorem grad_path_deriv (P : OCP) (k : ℕ) (x : Vec P.nx) (y u : PD P k) (t : ℝ)
    (hc : ContDiffAt ℝ 2 (lagr P k 0) (y + t • u)) :
    HasDerivAt (fun s : ℝ => grad P k x (y + s • u)) (hess P k (y + t • u) u) t := by
  have hp : HasDerivAt (fun s : ℝ => y + s • u) u t := by
    exact ((hasDerivAt_const t y).add ((hasDerivAt_id t).smul_const u)).congr_deriv (by simp)
  exact (grad_hasFDerivAt P k x _ hc).comp_hasDerivAt t hp

theorem grad_path_deriv_continuous (P : OCP) (k : ℕ) (y u : PD P k)
    (hc : ∀ t ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ 2 (lagr P k 0) (y + t • u)) :
    ContinuousOn (fun t : ℝ => hess P k (y + t • u) u) (Icc 0 1) := by
  intro t ht
  have hp : ContinuousAt (fun s : ℝ => y + s • u) t := by fun_prop
  have hh : ContinuousAt (fun s : ℝ => hess P k (y + s • u)) t :=
    (hess_continuousAt P k _ (hc t ht)).comp (f := fun s : ℝ => y + s • u) hp
  exact (hh.clm_apply continuousAt_const).continuousWithinAt

end RealTimeIter.Contract.RTIFresh
end

-- RTIProof.SuppliedIntegral

noncomputable section
namespace RealTimeIter.Contract.RTIFresh
open MeasureTheory

theorem supplied_integral_le {P : OCP} (ν : CompatNorms P) (k : ℕ)
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    (f : α → PD P k) (hf : Integrable f μ)
    (hn : Integrable (fun x => ν.nrm k (f x)) μ) :
    ν.nrm k (∫ x, f x ∂μ) ≤ ∫ x, ν.nrm k (f x) ∂μ := by
  exact (suppliedSeminorm ν k).convexOn.map_integral_le
    (supplied_continuous ν k).continuousOn isClosed_univ
    (Filter.Eventually.of_forall fun _ => Set.mem_univ _) hf hn

end RealTimeIter.Contract.RTIFresh
end

-- RTIProof.IntervalNorm

noncomputable section
namespace RealTimeIter.Contract.RTIFresh
open MeasureTheory Set

theorem supplied_interval_integral_le {P : OCP} (ν : CompatNorms P) (k : ℕ)
    (f : ℝ → PD P k) (hf : ContinuousOn f (Icc 0 1)) :
    ν.nrm k (∫ t in (0 : ℝ)..1, f t) ≤ ∫ t in (0 : ℝ)..1, ν.nrm k (f t) := by
  let μ : Measure ℝ := volume.restrict (Ioc 0 1)
  let : IsProbabilityMeasure μ := ⟨by simp [μ]⟩
  have hfi := hf.intervalIntegrable_of_Icc (μ := volume) (by norm_num : (0 : ℝ) ≤ 1)
  have hni := ((supplied_continuous ν k).comp_continuousOn hf).intervalIntegrable_of_Icc (μ := volume)
    (by norm_num : (0 : ℝ) ≤ 1)
  simpa only [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)] using
    supplied_integral_le ν k μ f hfi.1 hni.1

theorem supplied_interval_bound {P : OCP} (ν : CompatNorms P) (k : ℕ)
    (f : ℝ → PD P k) (hf : ContinuousOn f (Icc 0 1))
    (b : ℝ → ℝ) (hb : ContinuousOn b (Icc 0 1))
    (hle : ∀ t ∈ Icc (0 : ℝ) 1, ν.nrm k (f t) ≤ b t) :
    ν.nrm k (∫ t in (0 : ℝ)..1, f t) ≤ ∫ t in (0 : ℝ)..1, b t := by
  apply (supplied_interval_integral_le ν k f hf).trans
  exact intervalIntegral.integral_mono_on (by norm_num)
    (((supplied_continuous ν k).comp_continuousOn hf).intervalIntegrable_of_Icc (by norm_num))
    (hb.intervalIntegrable_of_Icc (by norm_num)) hle

end RealTimeIter.Contract.RTIFresh
end

-- RTIProof.FTCResidual

noncomputable section
namespace RealTimeIter.Contract.RTIFresh
open MeasureTheory Set

theorem supplied_ftc_residual {P : OCP} (ν : CompatNorms P) (k : ℕ)
    (F F' : ℝ → PD P k) (v : PD P k) (L : PD P k →L[ℝ] PD P k)
    (hF' : ContinuousOn F' (Icc 0 1))
    (hderiv : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt F (F' t) t)
    (hzero : F 0 + v = 0) (κ ω a : ℝ)
    (hbound : ∀ t ∈ Icc (0 : ℝ) 1,
      ν.nrm k (L (F' t - v)) ≤ κ * a + ω * t * a ^ 2) :
    ν.nrm k (L (F 1)) ≤ (κ + ω / 2 * a) * a := by
  have hi := hF'.intervalIntegrable_of_Icc (μ := volume) (by norm_num : (0 : ℝ) ≤ 1)
  have hFTC : (∫ t in (0 : ℝ)..1, F' t) = F 1 - F 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (by simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hderiv) hi
  have hconst : IntervalIntegrable (fun _ : ℝ => v) volume 0 1 := intervalIntegrable_const
  have he : (∫ t in (0 : ℝ)..1, F' t - v) = F 1 := by
    rw [intervalIntegral.integral_sub hi hconst, hFTC, intervalIntegral.integral_const]
    norm_num only [sub_zero, one_smul]
    have hv : v = -F 0 := by
      simpa only [add_sub_cancel_left, zero_sub] using congrArg (fun x => x - F 0) hzero
    rw [hv]
    abel
  have hL : (∫ t in (0 : ℝ)..1, L (F' t - v)) = L (F 1) := by
    rw [L.intervalIntegral_comp_comm (hi.sub hconst), he]
  have hcont : ContinuousOn (fun t => L (F' t - v)) (Icc (0 : ℝ) 1) :=
    L.continuous.comp_continuousOn (hF'.sub continuousOn_const)
  have hscalar : Continuous (fun t : ℝ => κ * a + ω * t * a ^ 2) := by fun_prop
  have hb := supplied_interval_bound ν k _ hcont _ hscalar.continuousOn hbound
  rw [hL] at hb
  have heval : (∫ t in (0 : ℝ)..1, κ * a + ω * t * a ^ 2) = (κ + ω / 2 * a) * a := by
    have hlin : IntervalIntegrable (fun t : ℝ => ω * t * a ^ 2) volume 0 1 :=
      (show Continuous (fun t : ℝ => ω * t * a ^ 2) from by fun_prop).intervalIntegrable 0 1
    rw [intervalIntegral.integral_add intervalIntegrable_const hlin,
      intervalIntegral.integral_const, intervalIntegral.integral_mul_const,
      intervalIntegral.integral_const_mul, integral_id]
    norm_num
    ring
  rw [heval] at hb
  exact hb

end RealTimeIter.Contract.RTIFresh
end

-- RTIProof.NativeLocalEstimate

noncomputable section
namespace RealTimeIter.Contract.RTIFresh
open Set

theorem native_local_estimate (P : OCP) (ν : CompatNorms P)
    (x0 : Vec P.nx) (y0 : PD P 0) (D0 : Set (PD P 0)) (κ ω : ℝ)
    (h : Thm41Hyp P ν x0 y0 D0 κ ω) (k : ℕ) (hk : k ≤ P.N)
    (x : Vec P.nx) (y : PD P k) (hy : y ∈ Dset P D0 k)
    (he : y + step P k x y ∈ Dset P D0 k)
    (hseg : ∀ t ∈ Icc (0 : ℝ) 1, y + t • step P k x y ∈ Dset P D0 k) :
    ν.nrm k (step P k x (y + step P k x y)) ≤
      (κ + ω / 2 * ν.nrm k (step P k x y)) * ν.nrm k (step P k x y) := by
  let u := step P k x y
  let L := (J P k (y + u)).inverse
  have hc : ∀ t ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ 2 (lagr P k 0) (y + t • u) :=
    fun t ht => h.c2 k hk _ (hseg t ht)
  have hz : grad P k x (y + (0 : ℝ) • u) + J P k y u = 0 := by
    simp only [zero_smul, add_zero]
    rw [step_residual P k x y (h.J_inv k hk y hy)]
    exact neg_add_cancel _
  have hb : ∀ t ∈ Icc (0 : ℝ) 1,
      ν.nrm k (L (hess P k (y + t • u) u - J P k y u)) ≤
        κ * ν.nrm k u + ω * t * ν.nrm k u ^ 2 := by
    intro t ht
    have ha := h.h41a k hk (y + u) he y hy t ht (by simpa only [add_sub_cancel_left] using hseg t ht)
    have hb := h.h41b k hk (y + u) he y hy t ht (by simpa only [add_sub_cancel_left] using hseg t ht)
    simp only [add_sub_cancel_left] at ha hb
    have heq : L (hess P k (y + t • u) u - J P k y u) =
        -(L ((J P k (y + t • u) - hess P k (y + t • u)) u)) +
          L ((J P k (y + t • u) - J P k y) u) := by
      simp only [sub_apply, map_sub]
      abel
    rw [heq]
    exact (ν.triangle k _ _).trans (by rw [supplied_neg]; exact add_le_add ha hb)
  have hr := supplied_ftc_residual ν k
    (fun t => grad P k x (y + t • u)) (fun t => hess P k (y + t • u) u)
    (J P k y u) L (grad_path_deriv_continuous P k y u hc)
    (fun t ht => grad_path_deriv P k x y u t (hc t ht)) hz κ ω (ν.nrm k u) hb
  simpa only [one_smul, step, supplied_neg, u, L] using hr

end RealTimeIter.Contract.RTIFresh
end

-- RTIProof.NativePositiveAssembly

noncomputable section
namespace RealTimeIter.Contract.RTIFresh
theorem native_positive_assembly (P : OCP) (ν : CompatNorms P) (x0 : Vec P.nx) (y0 : PD P 0)
    (D0 : Set (PD P 0)) (κ ω : ℝ) (h : Thm41Hyp P ν x0 y0 D0 κ ω) (hκ : 0 ≤ κ) (hω : 0 ≤ ω)
    (hlocal : ∀ k < P.N,
      (rti P x0 y0 k).2 ∈ projTo P k '' ball0 P ν x0 y0 κ ω →
      (rti P x0 y0 k).2 + rtiStep P x0 y0 k ∈ projTo P k '' ball0 P ν x0 y0 κ ω →
      ν.nrm (k + 1) (rtiStep P x0 y0 (k + 1)) ≤
        delta P ν x0 y0 κ ω k * ν.nrm k (rtiStep P x0 y0 k)) :
    -- (4.2)
    (∀ k ≤ P.N, (rti P x0 y0 k).2 ∈ projTo P k '' ball0 P ν x0 y0 κ ω ∧
        projTo P k '' ball0 P ν x0 y0 κ ω ⊆ Dset P D0 k) ∧
    -- (4.3)
    (∀ k < P.N,
        ν.nrm (k + 1) (rtiStep P x0 y0 (k + 1))
          ≤ (κ + ω / 2 * ν.nrm k (rtiStep P x0 y0 k)) * ν.nrm k (rtiStep P x0 y0 k) ∧
        delta P ν x0 y0 κ ω k * ν.nrm k (rtiStep P x0 y0 k)
          ≤ delta P ν x0 y0 κ ω 0 * ν.nrm k (rtiStep P x0 y0 k) ∧
        delta P ν x0 y0 κ ω k ≤ delta P ν x0 y0 κ ω 0) ∧
    -- (4.4)
    (∀ k ≤ P.N, ∃ ystar : PD P k,
        Filter.Tendsto (newtonIter P k (rti P x0 y0 k).1 (rti P x0 y0 k).2) Filter.atTop
          (nhds ystar) ∧
        grad P k (rti P x0 y0 k).1 ystar = 0 ∧
        ν.nrm k ((rti P x0 y0 k).2 - ystar)
          ≤ ν.nrm k (rtiStep P x0 y0 k) / (1 - delta P ν x0 y0 κ ω k) ∧
        ν.nrm k (rtiStep P x0 y0 k) / (1 - delta P ν x0 y0 κ ω k)
          ≤ delta P ν x0 y0 κ ω 0 ^ k * ν.nrm 0 (rtiStep P x0 y0 0)
              / (1 - delta P ν x0 y0 κ ω 0))  := by
  have hc := rti_positive_control ν x0 y0 κ ω hκ hω h.h41d hlocal
  have hb (k : ℕ) (hk : k ≤ P.N) :=
    rti_ball_consequences ν x0 y0 κ ω hκ hω h.h41d k (hc k hk).1 (hc k hk).2
  have hdom (k : ℕ) : projTo P k '' ball0 P ν x0 y0 κ ω ⊆ Dset P D0 k :=
    projected_ball_domain ν x0 y0 D0 κ ω h k
  have hd0 (k : ℕ) : 0 ≤ delta P ν x0 y0 κ ω k := by
    exact add_nonneg hκ (mul_nonneg (div_nonneg hω (by norm_num)) (supplied_nonneg ν k _))
  have hd1 (k : ℕ) (hk : k ≤ P.N) : delta P ν x0 y0 κ ω k < 1 :=
    (hb k hk).2.1.trans_lt h.h41d
  have hcorrected (k : ℕ) (hk : k ≤ P.N) :
      (rti P x0 y0 k).2 + rtiStep P x0 y0 k ∈ projTo P k '' ball0 P ν x0 y0 κ ω := by
    apply (hb k hk).2.2.2
    change ν.nrm k ((rti P x0 y0 k).2 + rtiStep P x0 y0 k - (rti P x0 y0 k).2) ≤ _
    rw [add_sub_cancel_left]
    apply (le_div_iff₀ (sub_pos.mpr (hd1 k hk))).mpr
    have ha := supplied_nonneg ν k (rtiStep P x0 y0 k)
    have hd := hd0 k
    nlinarith
  refine ⟨fun k hk => ⟨(hb k hk).1, hdom k⟩, ?_, ?_⟩
  · intro k hk
    have hk' : k ≤ P.N := hk.le
    exact ⟨hlocal k hk (hb k hk').1 (hcorrected k hk'),
      mul_le_mul_of_nonneg_right (hb k hk').2.1 (supplied_nonneg ν k _), (hb k hk').2.1⟩
  · intro k hk
    have hball : {z | ν.nrm k (z - (rti P x0 y0 k).2) ≤
        ν.nrm k (rtiStep P x0 y0 k) / (1 - delta P ν x0 y0 κ ω k)} ⊆ Dset P D0 k :=
      ((hb k hk).2.2.2).trans (hdom k)
    obtain ⟨l, hl, hg, he⟩ := native_newton_limit ν x0 y0 D0 κ ω h hκ hω k hk
      (rti P x0 y0 k).1 (rti P x0 y0 k).2 (hd1 k hk) hball
      (native_local_estimate P ν x0 y0 D0 κ ω h k hk (rti P x0 y0 k).1)
    exact ⟨l, hl, hg, he, (hb k hk).2.2.1⟩

end RealTimeIter.Contract.RTIFresh
end

-- RTIProof.NativeZeroBranch

noncomputable section
namespace RealTimeIter.Contract.RTIFresh
theorem native_zero_branch (P : OCP) (ν : CompatNorms P) (x0 : Vec P.nx) (y0 : PD P 0)
    (D0 : Set (PD P 0)) (κ ω : ℝ) (h : Thm41Hyp P ν x0 y0 D0 κ ω)
    (hsteps : ∀ k ≤ P.N, rtiStep P x0 y0 k = 0) :
    -- (4.2)
    (∀ k ≤ P.N, (rti P x0 y0 k).2 ∈ projTo P k '' ball0 P ν x0 y0 κ ω ∧
        projTo P k '' ball0 P ν x0 y0 κ ω ⊆ Dset P D0 k) ∧
    -- (4.3)
    (∀ k < P.N,
        ν.nrm (k + 1) (rtiStep P x0 y0 (k + 1))
          ≤ (κ + ω / 2 * ν.nrm k (rtiStep P x0 y0 k)) * ν.nrm k (rtiStep P x0 y0 k) ∧
        delta P ν x0 y0 κ ω k * ν.nrm k (rtiStep P x0 y0 k)
          ≤ delta P ν x0 y0 κ ω 0 * ν.nrm k (rtiStep P x0 y0 k) ∧
        delta P ν x0 y0 κ ω k ≤ delta P ν x0 y0 κ ω 0) ∧
    -- (4.4)
    (∀ k ≤ P.N, ∃ ystar : PD P k,
        Filter.Tendsto (newtonIter P k (rti P x0 y0 k).1 (rti P x0 y0 k).2) Filter.atTop
          (nhds ystar) ∧
        grad P k (rti P x0 y0 k).1 ystar = 0 ∧
        ν.nrm k ((rti P x0 y0 k).2 - ystar)
          ≤ ν.nrm k (rtiStep P x0 y0 k) / (1 - delta P ν x0 y0 κ ω k) ∧
        ν.nrm k (rtiStep P x0 y0 k) / (1 - delta P ν x0 y0 κ ω k)
          ≤ delta P ν x0 y0 κ ω 0 ^ k * ν.nrm 0 (rtiStep P x0 y0 0)
              / (1 - delta P ν x0 y0 κ ω 0))  := by
  have hzero := hsteps 0 (Nat.zero_le _)
  have hy0 : y0 ∈ ball0 P ν x0 y0 κ ω := by
    simp [ball0, hzero, supplied_zero]
  have hmem (k : ℕ) (hk : k ≤ P.N) :
      (rti P x0 y0 k).2 ∈ projTo P k '' ball0 P ν x0 y0 κ ω :=
    ⟨y0, hy0, (rti_zero_iterates P x0 y0 hsteps k hk).symm⟩
  have hdom (k : ℕ) : projTo P k '' ball0 P ν x0 y0 κ ω ⊆ Dset P D0 k :=
    projected_ball_domain ν x0 y0 D0 κ ω h k
  have hd (k : ℕ) (hk : k ≤ P.N) : delta P ν x0 y0 κ ω k = κ := by
    simp [delta, hsteps k hk, supplied_zero]
  refine ⟨fun k hk => ⟨hmem k hk, hdom k⟩, ?_, ?_⟩
  · intro k hk
    simp [hsteps k (by omega), hsteps (k + 1) (by omega), supplied_zero,
      hd k (by omega), hd 0 (Nat.zero_le _)]
  · intro k hk
    let xy := rti P x0 y0 k
    have hs : step P k xy.1 xy.2 = 0 := hsteps k hk
    have hg : grad P k xy.1 xy.2 = 0 :=
      (step_zero_iff P k xy.1 xy.2 (h.J_inv k hk _ (hdom k (hmem k hk)))).mp hs
    refine ⟨xy.2, newton_tendsto_of_step_zero P k xy.1 xy.2 hs, hg, ?_, ?_⟩
    · simp [xy, hsteps k hk, supplied_zero]
    · simp [hsteps k hk, hzero, supplied_zero]

end RealTimeIter.Contract.RTIFresh
end

-- RTIProof.MultiplierCoordinates

noncomputable section
namespace RealTimeIter.Contract.RTIFresh
open scoped InnerProductSpace

def lamT (P : OCP) (k i : ℕ) : Vec P.nx →L[ℝ] PD P k :=
  pull (fun c => match c.1 with
    | Sum.inl (i', j) => if i'.val = i then some j else none
    | _ => none)

theorem lamT_apply (P : OCP) (k i : ℕ) (v : Vec P.nx)
    (c : {c : Coord P // k ≤ stage c}) :
    lamT P k i v c = match c.1 with
      | Sum.inl (i', j) => if i'.val = i then v j else 0
      | _ => 0 := by
  unfold lamT
  rw [pull_apply]
  rcases c with ⟨c,hc⟩
  rcases c with ⟨i',j⟩ | c
  · dsimp only
    split_ifs <;> rfl
  · rcases c with c | c <;> rfl

theorem sL_lamT (P : OCP) (k i j : ℕ) (v : Vec P.nx) :
    sL P k i (lamT P k j v) = 0 := by
  ext a
  rw [sL_apply]
  split_ifs
  · change lamT P k j v _ = 0
    rw [lamT_apply]
  · rfl

theorem qL_lamT (P : OCP) (k i j : ℕ) (v : Vec P.nx) :
    qL P k i (lamT P k j v) = 0 := by
  ext a
  rw [qL_apply]
  split_ifs
  · change lamT P k j v _ = 0
    rw [lamT_apply]
  · rfl

theorem lamL_lamT (P : OCP) (k i j : ℕ) (v : Vec P.nx)
    (hi : i < P.N + 1) (hki : k ≤ i) :
    lamL P k i (lamT P k j v) = if i = j then v else 0 := by
  ext a
  rw [lamL_apply, dif_pos (And.intro hi hki)]
  change lamT P k j v _ = _
  rw [lamT_apply]
  dsimp only
  split_ifs <;> rfl

theorem lamL_inner_lamT (P : OCP) (k i : ℕ) (hi : i < P.N + 1) (hki : k ≤ i)
    (y : PD P k) (v : Vec P.nx) : ⟪lamL P k i y, v⟫_ℝ = ⟪y, lamT P k i v⟫_ℝ := by
  classical
  simp only [PiLp.inner_apply, Real.inner_apply]
  let S : Finset {c : Coord P // k ≤ stage c} := Finset.univ.filter
    (fun c => ∃ a : Fin P.nx, c.val = Sum.inl (⟨i,hi⟩,a))
  calc
    _ = ∑ c ∈ S, y c * lamT P k i v c := by
      apply Finset.sum_bij (fun a _ => ⟨Sum.inl (⟨i,hi⟩,a),hki⟩)
      · intro a ha
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, a, rfl⟩
      · intro a ha b hb hab
        have he := congrArg (fun c : {c : Coord P // k ≤ stage c} => c.val) hab
        simpa using he
      · intro b hb
        obtain ⟨a,ha⟩ := (Finset.mem_filter.mp hb).2
        exact ⟨a, Finset.mem_univ _, Subtype.ext ha.symm⟩
      · intro a ha
        simp only [lamL_apply, dif_pos (And.intro hi hki), lamT_apply]
        simp only [ite_true]
    _ = _ := by
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro c hc hn
      have hn' : ¬ ∃ a : Fin P.nx, c.val = Sum.inl (⟨i,hi⟩,a) := by simpa [S] using hn
      rcases c with ⟨c,hc⟩
      rcases c with ⟨i',a⟩ | c
      · have hne : i'.val ≠ i := by
          intro he
          apply hn'
          have hh : i' = ⟨i,hi⟩ := Fin.ext he
          subst i'
          exact ⟨a, rfl⟩
        simp only [lamT_apply, if_neg hne, mul_zero]
      · rcases c with c | c <;> simp only [lamT_apply, mul_zero]

end RealTimeIter.Contract.RTIFresh
end

-- RTIProof.MultiplierLagrangian

noncomputable section
namespace RealTimeIter.Contract.RTIFresh
open scoped InnerProductSpace

theorem lagr_multiplier_shift (P : OCP) (k : ℕ) (hk : k ≤ P.N)
    (x : Vec P.nx) (y : PD P k) (v : Vec P.nx) :
    lagr P k x (y + lamT P k k v) = lagr P k x y + ⟪v, x - sL P k k y⟫_ℝ := by
  have hc : (∑ i ∈ Finset.Ico k P.N,
      ⟪lamL P k (i + 1) (y + lamT P k k v),
        P.f i (sL P k i y) (qL P k i y) - sL P k (i + 1) y⟫_ℝ) =
      ∑ i ∈ Finset.Ico k P.N,
      ⟪lamL P k (i + 1) y, P.f i (sL P k i y) (qL P k i y) - sL P k (i + 1) y⟫_ℝ := by
    apply Finset.sum_congr rfl
    intro i hi
    obtain ⟨hki,hiN⟩ := Finset.mem_Ico.mp hi
    rw [map_add, lamL_lamT P k (i+1) k v (by omega) (by omega), if_neg (by omega), add_zero]
  simp only [map_add] at hc
  simp only [lagr, map_add, sL_lamT, qL_lamT, add_zero]
  rw [hc, lamL_lamT P k k k v (by omega) le_rfl, if_pos rfl, inner_add_left]
  ring

theorem grad_multiplier_row (P : OCP) (k : ℕ) (hk : k ≤ P.N)
    (x : Vec P.nx) (y : PD P k) (hc : ContDiffAt ℝ 2 (lagr P k 0) y) :
    lamL P k k (grad P k x y) = x - sL P k k y := by
  let b := x - sL P k k y
  let L : Vec P.nx →L[ℝ] ℝ := InnerProductSpace.toDual ℝ (Vec P.nx) b
  have he : ∀ v, lagr P k x (y + lamT P k k v) = L v + lagr P k x y := by
    intro v
    rw [lagr_multiplier_shift P k hk]
    simp only [L, InnerProductSpace.toDual_apply_apply, b, real_inner_comm]
    ring
  have hf : DifferentiableAt ℝ (lagr P k x) (y + lamT P k k 0) := by
    simpa only [map_zero, add_zero] using
      (lagr_contDiffAt_initial P k x y hc).differentiableAt (by norm_num)
  have hh := gradient_affine_restriction (lamT P k k) (lamL P k k)
    (lamL_inner_lamT P k k (by omega) le_rfl) (lagr P k x) L y (lagr P k x y)
    he 0 hf L.differentiableAt
  have hg : gradient L (0 : Vec P.nx) = b := by
    change (InnerProductSpace.toDual ℝ (Vec P.nx)).symm (fderiv ℝ L 0) = b
    rw [L.hasFDerivAt.fderiv]
    exact (InnerProductSpace.toDual ℝ (Vec P.nx)).symm_apply_apply b
  simpa only [map_zero, add_zero, hg, grad] using hh

end RealTimeIter.Contract.RTIFresh
end

-- RTIProof.MultiplierHessian

noncomputable section
namespace RealTimeIter.Contract.RTIFresh
open Filter

theorem lamL_sT (P : OCP) (k i j : ℕ) (v : Vec P.nx) : lamL P k i (sT P k j v) = 0 := by
  ext a
  rw [lamL_apply]
  split_ifs
  · change sT P k j v _ = 0
    unfold sT
    rw [pull_apply]
  · rfl

theorem lamL_qT (P : OCP) (k i j : ℕ) (v : Vec P.nu) : lamL P k i (qT P k j v) = 0 := by
  ext a
  rw [lamL_apply]
  split_ifs
  · change qT P k j v _ = 0
    unfold qT
    rw [pull_apply]
  · rfl

theorem hess_multiplier_row (P : OCP) (k : ℕ) (hk : k ≤ P.N) (y : PD P k)
    (hc : ContDiffAt ℝ 2 (lagr P k 0) y) :
    (lamL P k k).comp (hess P k y) = -sL P k k := by
  have ha := (lamL P k k).hasFDerivAt.comp y (grad_hasFDerivAt P k 0 y hc)
  have hb := (hasFDerivAt_const (0 : Vec P.nx) y).sub (sL P k k).hasFDerivAt
  have he : (fun z => (0 : Vec P.nx) - sL P k k z) =ᶠ[nhds y]
      (fun z => lamL P k k (grad P k 0 z)) := by
    filter_upwards [hc.eventually (by norm_num)] with z hz
    exact (grad_multiplier_row P k hk 0 z hz).symm
  have heq := (ha.congr_of_eventuallyEq he).unique hb
  simpa only [zero_sub] using heq

theorem J_multiplier_row (P : OCP) (k : ℕ) (hk : k ≤ P.N) (y u : PD P k)
    (hc : ContDiffAt ℝ 2 (lagr P k 0) y) :
    lamL P k k (J P k y u) = -sL P k k u := by
  have hh := congrArg (fun T : PD P k →L[ℝ] Vec P.nx => T u) (hess_multiplier_row P k hk y hc)
  simp only [ContinuousLinearMap.comp_apply, neg_apply] at hh
  simp only [J, add_apply, sum_apply,
    ContinuousLinearMap.comp_apply, map_add, map_sum, embSQ,
    ContinuousLinearMap.coprod_apply, lamL_sT, lamL_qT, add_zero, Finset.sum_const_zero]
  exact hh

theorem step_initial_state (P : OCP) (k : ℕ) (hk : k ≤ P.N)
    (x : Vec P.nx) (y : PD P k) (hc : ContDiffAt ℝ 2 (lagr P k 0) y)
    (hi : (J P k y).IsInvertible) : sL P k k (y + step P k x y) = x := by
  have he := congrArg (lamL P k k) (step_residual P k x y hi)
  rw [grad_multiplier_row P k hk x y hc, map_neg, J_multiplier_row P k hk y _ hc, neg_neg] at he
  rw [map_add, ← he, add_sub_cancel]

end RealTimeIter.Contract.RTIFresh
end

-- RTIProof.ZeroStepTransition

noncomputable section
namespace RealTimeIter.Contract.RTIFresh

theorem zero_step_transition (P : OCP) (k : ℕ) (hk : k < P.N)
    (x : Vec P.nx) (y : PD P k) (hc : ContDiffAt ℝ 2 (lagr P k 0) y)
    (hd : ContDiffAt ℝ 2 (lagr P (k + 1) 0) (proj P k y))
    (hi : (J P k y).IsInvertible) (hz : step P k x y = 0) :
    step P (k + 1) (P.f k x (qL P k k y)) (proj P k y) = 0 := by
  have hs := step_initial_state P k hk.le x y hc hi
  simp only [hz, add_zero] at hs
  have hg : grad P k x y = 0 := (step_zero_iff P k x y hi).mp hz
  have hc' : ContDiffAt ℝ 2 (lagr P k 0) (y + projT P k 0) := by
    simpa only [map_zero, add_zero] using hc
  have hd' : ContDiffAt ℝ 2 (lagr P (k + 1) 0) (proj P k y + 0) := by
    simpa only [add_zero] using hd
  have he := grad_affine_restriction P k hk x y 0 hc' hd'
  simp only [map_zero, add_zero, hs, hg] at he
  simp only [step, ← he, map_zero, neg_zero]

theorem rti_zero_steps (P : OCP) (ν : CompatNorms P)
    (x0 : Vec P.nx) (y0 : PD P 0) (D0 : Set (PD P 0)) (κ ω : ℝ)
    (h : Thm41Hyp P ν x0 y0 D0 κ ω) (hz : rtiStep P x0 y0 0 = 0) :
    ∀ k ≤ P.N, (rti P x0 y0 k).2 ∈ Dset P D0 k ∧ rtiStep P x0 y0 k = 0 := by
  intro k
  induction k with
  | zero => intro hk; exact ⟨h.mem,hz⟩
  | succ k ih =>
    intro hk
    obtain ⟨hmem,hstep⟩ := ih (by omega)
    have hmnext : proj P k (rti P x0 y0 k).2 ∈ Dset P D0 (k + 1) := ⟨_,hmem,rfl⟩
    have hsnext := zero_step_transition P k (by omega) (rti P x0 y0 k).1 (rti P x0 y0 k).2
      (h.c2 k (by omega) _ hmem) (h.c2 (k+1) hk _ hmnext) (h.J_inv k (by omega) _ hmem) hstep
    have hs : step P k (rti P x0 y0 k).1 (rti P x0 y0 k).2 = 0 := hstep
    constructor
    · simpa only [rti, hs, add_zero] using hmnext
    · simpa only [rtiStep, rti, hs, add_zero] using hsnext

end RealTimeIter.Contract.RTIFresh
end

-- RTIProof.PrimalProjection

noncomputable section
namespace RealTimeIter.Contract.RTIFresh

theorem sT_apply (P : OCP) (k i : ℕ) (v : Vec P.nx)
    (c : {c : Coord P // k ≤ stage c}) :
    sT P k i v c = match c.1 with
      | Sum.inr (Sum.inl (i', j)) => if i'.val = i then v j else 0
      | _ => 0 := by
  unfold sT
  rw [pull_apply]
  rcases c with ⟨c, hc⟩
  rcases c with c | c
  · rfl
  · rcases c with c | c
    · rcases c with ⟨j, l⟩
      dsimp only
      split_ifs <;> rfl
    · rfl

theorem qT_apply (P : OCP) (k i : ℕ) (v : Vec P.nu)
    (c : {c : Coord P // k ≤ stage c}) :
    qT P k i v c = match c.1 with
      | Sum.inr (Sum.inr (i', j)) => if i'.val = i then v j else 0
      | _ => 0 := by
  unfold qT
  rw [pull_apply]
  rcases c with ⟨c, hc⟩
  rcases c with c | c
  · rfl
  · rcases c with c | c
    · rfl
    · rcases c with ⟨j, l⟩
      dsimp only
      split_ifs <;> rfl

theorem proj_sT (P : OCP) (k i : ℕ) (v : Vec P.nx) :
    proj P k (sT P k i v) = sT P (k + 1) i v := by
  ext c
  simp only [proj_apply, sT_apply]

theorem proj_qT (P : OCP) (k i : ℕ) (v : Vec P.nu) :
    proj P k (qT P k i v) = qT P (k + 1) i v := by
  ext c
  simp only [proj_apply, qT_apply]

theorem sT_below (P : OCP) (k i : ℕ) (hi : i < k) (v : Vec P.nx) :
    sT P k i v = 0 := by
  ext c
  rcases c with ⟨c, hc⟩
  rcases c with c | c
  · simp only [sT_apply, PiLp.zero_apply]
  · rcases c with c | c
    · rcases c with ⟨j, l⟩
      have hj : j.val ≠ i := by change k ≤ j.val at hc; omega
      simp only [sT_apply, hj, ↓reduceIte, PiLp.zero_apply]
    · simp only [sT_apply, PiLp.zero_apply]

theorem qT_below (P : OCP) (k i : ℕ) (hi : i < k) (v : Vec P.nu) :
    qT P k i v = 0 := by
  ext c
  rcases c with ⟨c, hc⟩
  rcases c with c | c
  · simp only [qT_apply, PiLp.zero_apply]
  · rcases c with c | c
    · simp only [qT_apply, PiLp.zero_apply]
    · rcases c with ⟨j, l⟩
      have hj : j.val ≠ i := by change k ≤ j.val at hc; omega
      simp only [qT_apply, hj, ↓reduceIte, PiLp.zero_apply]

theorem projT_sT (P : OCP) (k i : ℕ) (hi : k + 1 ≤ i) (v : Vec P.nx) :
    projT P k (sT P (k + 1) i v) = sT P k i v := by
  ext c
  rw [projT_apply]
  split_ifs with hc
  · simp only [sT_apply]
  · rcases c with ⟨c, hc'⟩
    rcases c with c | c
    · simp only [sT_apply]
    · rcases c with c | c
      · rcases c with ⟨j, l⟩
        have hj : j.val ≠ i := by change ¬k + 1 ≤ j.val at hc; omega
        simp only [sT_apply, hj, ↓reduceIte]
      · simp only [sT_apply]

theorem projT_qT (P : OCP) (k i : ℕ) (hi : k + 1 ≤ i) (v : Vec P.nu) :
    projT P k (qT P (k + 1) i v) = qT P k i v := by
  ext c
  rw [projT_apply]
  split_ifs with hc
  · simp only [qT_apply]
  · rcases c with ⟨c, hc'⟩
    rcases c with c | c
    · simp only [qT_apply]
    · rcases c with c | c
      · simp only [qT_apply]
      · rcases c with ⟨j, l⟩
        have hj : j.val ≠ i := by change ¬k + 1 ≤ j.val at hc; omega
        simp only [qT_apply, hj, ↓reduceIte]

theorem blockSQ_proj (P : OCP) (k i : ℕ) (hi : k + 1 ≤ i) (y : PD P k) :
    blockSQ P (k + 1) i (proj P k y) = blockSQ P k i y := by
  exact Prod.ext (sL_proj P k i hi y) (qL_proj P k i hi y)

theorem blockSQ_projT (P : OCP) (k i : ℕ) (y : PD P (k + 1)) :
    blockSQ P k i (projT P k y) = blockSQ P (k + 1) i y := by
  exact Prod.ext (sL_projT P k i y) (qL_projT P k i y)

theorem proj_embSQ (P : OCP) (k i : ℕ) (v : Vec P.nx × Vec P.nu) :
    proj P k (embSQ P k i v) = embSQ P (k + 1) i v := by
  change proj P k (sT P k i v.1 + qT P k i v.2) = _
  rw [map_add, proj_sT, proj_qT]
  rfl

theorem projT_embSQ (P : OCP) (k i : ℕ) (hi : k + 1 ≤ i) (v : Vec P.nx × Vec P.nu) :
    projT P k (embSQ P (k + 1) i v) = embSQ P k i v := by
  change projT P k (sT P (k + 1) i v.1 + qT P (k + 1) i v.2) = _
  rw [map_add, projT_sT P k i hi, projT_qT P k i hi]
  rfl

theorem proj_embSQ_current (P : OCP) (k : ℕ) (v : Vec P.nx × Vec P.nu) :
    proj P k (embSQ P k k v) = 0 := by
  rw [proj_embSQ]
  change sT P (k + 1) k v.1 + qT P (k + 1) k v.2 = 0
  rw [sT_below P (k + 1) k (by omega), qT_below P (k + 1) k (by omega), zero_add]

end RealTimeIter.Contract.RTIFresh
end

-- RTIProof.HessianProjection

noncomputable section
namespace RealTimeIter.Contract.RTIFresh
open Filter

theorem hess_project_restrict (P : OCP) (k : ℕ) (hk : k < P.N) (y : PD P k)
    (hc : ContDiffAt ℝ 2 (lagr P k 0) y)
    (hd : ContDiffAt ℝ 2 (lagr P (k + 1) 0) (proj P k y)) :
    (proj P k).comp ((hess P k y).comp (projT P k)) = hess P (k + 1) (proj P k y) := by
  let x' := P.f k (sL P k k y) (qL P k k y)
  have hleft : HasFDerivAt (fun z : PD P (k + 1) => proj P k (grad P k 0 (y + projT P k z)))
      ((proj P k).comp ((hess P k y).comp (projT P k))) 0 := by
    have hb : HasFDerivAt (grad P k 0) (hess P k y) (y + projT P k 0) := by
      simpa only [map_zero, add_zero] using grad_hasFDerivAt P k 0 y hc
    have hp : HasFDerivAt (fun z : PD P (k + 1) => y + projT P k z) (projT P k) 0 := by
      exact ((hasFDerivAt_const y (0 : PD P (k + 1))).add (projT P k).hasFDerivAt).congr_fderiv (zero_add _)
    have hh := hb.comp 0 hp
    exact (proj P k).hasFDerivAt.comp 0 hh
  have hright : HasFDerivAt (fun z : PD P (k + 1) => grad P (k + 1) x' (proj P k y + z))
      (hess P (k + 1) (proj P k y)) 0 := by
    have hb : HasFDerivAt (grad P (k + 1) x') (hess P (k + 1) (proj P k y)) (proj P k y + 0) := by
      simpa only [add_zero] using grad_hasFDerivAt P (k + 1) x' (proj P k y) hd
    have hp : HasFDerivAt (fun z : PD P (k + 1) => proj P k y + z) (ContinuousLinearMap.id ℝ _) 0 := by
      exact ((hasFDerivAt_const (proj P k y) (0 : PD P (k + 1))).add (hasFDerivAt_id 0)).congr_fderiv (zero_add _)
    have hh := hb.comp 0 hp
    exact hh.congr_fderiv (ContinuousLinearMap.comp_id _)
  have hcy : Tendsto (fun z : PD P (k + 1) => y + projT P k z) (nhds 0) (nhds y) := by
    have hh : Continuous (fun z : PD P (k + 1) => y + projT P k z) := by fun_prop
    simpa only [map_zero, add_zero] using hh.tendsto 0
  have hdy : Tendsto (fun z : PD P (k + 1) => proj P k y + z) (nhds 0) (nhds (proj P k y)) := by
    have hh : Continuous (fun z : PD P (k + 1) => proj P k y + z) := by fun_prop
    simpa only [add_zero] using hh.tendsto 0
  have he : (fun z : PD P (k + 1) => grad P (k + 1) x' (proj P k y + z)) =ᶠ[nhds 0]
      (fun z => proj P k (grad P k 0 (y + projT P k z))) := by
    filter_upwards [hcy.eventually (hc.eventually (by norm_num)), hdy.eventually (hd.eventually (by norm_num))] with z hz hz'
    exact (grad_affine_restriction P k hk 0 y z hz hz').symm
  exact (hleft.congr_of_eventuallyEq he).unique hright

end RealTimeIter.Contract.RTIFresh
end

-- RTIProof.CorrectionBlocks

noncomputable section
namespace RealTimeIter.Contract.RTIFresh

def primalCorrection (P : OCP) (k : ℕ) (y : PD P k) (i : ℕ) (v : PD P k) : PD P k :=
  embSQ P k i (P.QH i (sL P k i y) (qL P k i y) (lamL P k (i + 1) y) (blockSQ P k i v) -
    blockSQ P k i (hess P k y (embSQ P k i (blockSQ P k i v))))

def terminalCorrection (P : OCP) (k : ℕ) (y v : PD P k) : PD P k :=
  sT P k P.N (P.QHN (sL P k P.N y) (sL P k P.N v) -
    sL P k P.N (hess P k y (sT P k P.N (sL P k P.N v))))

theorem J_sub_hess_apply (P : OCP) (k : ℕ) (y v : PD P k) :
    (J P k y - hess P k y) v =
      (∑ i ∈ Finset.Ico k P.N, primalCorrection P k y i v) + terminalCorrection P k y v := by
  simp only [J, sub_apply, add_apply,
    sum_apply, ContinuousLinearMap.comp_apply,
    primalCorrection, terminalCorrection]
  abel

theorem projected_primal_hessian (P : OCP) (k : ℕ) (hk : k < P.N) (y : PD P k)
    (hc : ContDiffAt ℝ 2 (lagr P k 0) y)
    (hd : ContDiffAt ℝ 2 (lagr P (k + 1) 0) (proj P k y))
    (i : ℕ) (hi : k + 1 ≤ i) (w : Vec P.nx × Vec P.nu) :
    blockSQ P k i (hess P k y (embSQ P k i w)) =
      blockSQ P (k + 1) i (hess P (k + 1) (proj P k y) (embSQ P (k + 1) i w)) := by
  have hh := congrArg (fun L : PD P (k + 1) →L[ℝ] PD P (k + 1) => L (embSQ P (k + 1) i w))
    (hess_project_restrict P k hk y hc hd)
  simp only [ContinuousLinearMap.comp_apply, projT_embSQ P k i hi] at hh
  rw [← blockSQ_proj P k i hi, hh]

theorem primalCorrection_project (P : OCP) (k : ℕ) (hk : k < P.N) (y v : PD P k)
    (hc : ContDiffAt ℝ 2 (lagr P k 0) y)
    (hd : ContDiffAt ℝ 2 (lagr P (k + 1) 0) (proj P k y))
    (i : ℕ) (hi : k + 1 ≤ i) :
    proj P k (primalCorrection P k y i v) =
      primalCorrection P (k + 1) (proj P k y) i (proj P k v) := by
  simp only [primalCorrection, proj_embSQ, sL_proj P k i hi, qL_proj P k i hi,
    lamL_proj P k (i + 1) (by omega), blockSQ_proj P k i hi]
  rw [projected_primal_hessian P k hk y hc hd i hi]

theorem primalCorrection_current (P : OCP) (k : ℕ) (y v : PD P k) :
    proj P k (primalCorrection P k y k v) = 0 := by
  exact proj_embSQ_current P k _

theorem terminalCorrection_project (P : OCP) (k : ℕ) (hk : k < P.N) (y v : PD P k)
    (hc : ContDiffAt ℝ 2 (lagr P k 0) y)
    (hd : ContDiffAt ℝ 2 (lagr P (k + 1) 0) (proj P k y)) :
    proj P k (terminalCorrection P k y v) =
      terminalCorrection P (k + 1) (proj P k y) (proj P k v) := by
  have hi : k + 1 ≤ P.N := hk
  have hh := congrArg (fun L : PD P (k + 1) →L[ℝ] PD P (k + 1) =>
    L (sT P (k + 1) P.N (sL P k P.N v))) (hess_project_restrict P k hk y hc hd)
  simp only [ContinuousLinearMap.comp_apply, projT_sT P k P.N hi] at hh
  have hb : sL P k P.N (hess P k y (sT P k P.N (sL P k P.N v))) =
      sL P (k + 1) P.N (hess P (k + 1) (proj P k y) (sT P (k + 1) P.N (sL P k P.N v))) := by
    rw [← sL_proj P k P.N hi, hh]
  simp only [terminalCorrection, proj_sT, sL_proj P k P.N hi]
  rw [hb]

end RealTimeIter.Contract.RTIFresh
end

-- RTIProof.CorrectionTransport

noncomputable section
namespace RealTimeIter.Contract.RTIFresh

theorem correction_project (P : OCP) (k : ℕ) (hk : k < P.N) (y v : PD P k)
    (hc : ContDiffAt ℝ 2 (lagr P k 0) y)
    (hd : ContDiffAt ℝ 2 (lagr P (k + 1) 0) (proj P k y)) :
    proj P k ((J P k y - hess P k y) v) =
      (J P (k + 1) (proj P k y) - hess P (k + 1) (proj P k y)) (proj P k v) := by
  rw [J_sub_hess_apply, map_add, map_sum, J_sub_hess_apply]
  rw [Finset.sum_eq_sum_Ico_succ_bot hk, primalCorrection_current, zero_add]
  rw [terminalCorrection_project P k hk y v hc hd]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  exact primalCorrection_project P k hk y v hc hd i (Finset.mem_Ico.mp hi).1

end RealTimeIter.Contract.RTIFresh
end

-- RTIProof.StepGradientTransition

noncomputable section
namespace RealTimeIter.Contract.RTIFresh

theorem step_gradient_transition (P : OCP) (k : ℕ) (hk : k < P.N)
    (x : Vec P.nx) (y : PD P k)
    (hc : ContDiffAt ℝ 2 (lagr P k 0) y)
    (he : ContDiffAt ℝ 2 (lagr P k 0) (y + step P k x y))
    (hd : ContDiffAt ℝ 2 (lagr P (k+1) 0) (proj P k (y + step P k x y)))
    (hi : (J P k y).IsInvertible) :
    grad P (k+1) (P.f k x (qL P k k (y + step P k x y))) (proj P k (y + step P k x y)) =
      proj P k (grad P k x (y + step P k x y)) := by
  have hs := step_initial_state P k hk.le x y hc hi
  have he' : ContDiffAt ℝ 2 (lagr P k 0) ((y + step P k x y) + projT P k 0) := by
    simpa only [map_zero,add_zero] using he
  have hd' : ContDiffAt ℝ 2 (lagr P (k+1) 0) (proj P k (y + step P k x y) + 0) := by
    simpa only [add_zero] using hd
  have hh := grad_affine_restriction P k hk x (y + step P k x y) 0 he' hd'
  simpa only [map_zero,add_zero,hs] using hh.symm

end RealTimeIter.Contract.RTIFresh
end

-- RTIProof.FTCResidualCross

noncomputable section
namespace RealTimeIter.Contract.RTIFresh
open Set

theorem supplied_ftc_residual_cross {P : OCP} (ν : CompatNorms P) (k ℓ : ℕ)
    (F F' : ℝ → PD P k) (v : PD P k) (L : PD P k →L[ℝ] PD P ℓ)
    (hF' : ContinuousOn F' (Icc 0 1))
    (hderiv : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt F (F' t) t)
    (hzero : F 0 + v = 0) (κ ω a : ℝ)
    (hbound : ∀ t ∈ Icc (0 : ℝ) 1,
      ν.nrm ℓ (L (F' t - v)) ≤ κ * a + ω * t * a ^ 2) :
    ν.nrm ℓ (L (F 1)) ≤ (κ + ω / 2 * a) * a := by
  have hz : L (F 0) + L v = 0 := by
    simpa only [map_add, map_zero] using congrArg L hzero
  have hd : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt (fun s => L (F s)) (L (F' t)) t := by
    intro t ht
    exact L.hasFDerivAt.comp_hasDerivAt t (hderiv t ht)
  have hb : ∀ t ∈ Icc (0 : ℝ) 1,
      ν.nrm ℓ ((ContinuousLinearMap.id ℝ (PD P ℓ)) (L (F' t) - L v)) ≤
        κ * a + ω * t * a ^ 2 := by
    intro t ht
    simpa only [ContinuousLinearMap.id_apply, ← map_sub] using hbound t ht
  exact supplied_ftc_residual ν ℓ (fun t => L (F t)) (fun t => L (F' t)) (L v)
    (ContinuousLinearMap.id ℝ (PD P ℓ)) (L.continuous.comp_continuousOn hF') hd hz κ ω a hb

end RealTimeIter.Contract.RTIFresh
end

-- RTIProof.NativeProjectedEstimate

noncomputable section
namespace RealTimeIter.Contract.RTIFresh
open Set

theorem native_projected_estimate (P : OCP) (ν : CompatNorms P)
    (x0 : Vec P.nx) (y0 : PD P 0) (D0 : Set (PD P 0)) (κ ω : ℝ)
    (h : Thm41Hyp P ν x0 y0 D0 κ ω) (hκ : 0 ≤ κ) (k : ℕ) (hk : k < P.N)
    (x : Vec P.nx) (y : PD P k) (hy : y ∈ Dset P D0 k)
    (he : y + step P k x y ∈ Dset P D0 k)
    (hseg : ∀ t ∈ Icc (0 : ℝ) 1, y + t • step P k x y ∈ Dset P D0 k) :
    ν.nrm (k+1) (step P (k+1) (P.f k x (qL P k k (y + step P k x y)))
      (proj P k (y + step P k x y))) ≤
      (κ + ω / 2 * ν.nrm k (step P k x y)) * ν.nrm k (step P k x y) := by
  let u := step P k x y
  let L := (J P (k+1) (proj P k (y+u))).inverse.comp (proj P k)
  have hp (z : PD P k) (hz : z ∈ Dset P D0 k) : proj P k z ∈ Dset P D0 (k+1) := ⟨z,hz,rfl⟩
  have hc : ∀ t ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ 2 (lagr P k 0) (y + t • u) :=
    fun t ht => h.c2 k hk.le _ (hseg t ht)
  have hz : grad P k x (y + (0 : ℝ) • u) + J P k y u = 0 := by
    simp only [zero_smul,add_zero]
    rw [step_residual P k x y (h.J_inv k hk.le y hy)]
    exact neg_add_cancel _
  have hb : ∀ t ∈ Icc (0 : ℝ) 1,
      ν.nrm (k+1) (L (hess P k (y+t•u) u - J P k y u)) ≤
        κ * ν.nrm k u + ω * t * ν.nrm k u ^ 2 := by
    intro t ht
    have hpt : proj P k y + t • (proj P k (y+u) - proj P k y) ∈ Dset P D0 (k+1) := by
      simpa only [map_add,map_smul,add_sub_cancel_left] using hp _ (hseg t ht)
    have ha := h.h41a (k+1) (by omega) _ (hp _ he) _ (hp _ hy) t ht hpt
    have hb := h.h41c k hk (y+u) he y hy t ht (by simpa only [add_sub_cancel_left] using hseg t ht)
    simp only [map_add,add_sub_cancel_left] at ha
    simp only [add_sub_cancel_left] at hb
    have hcorr := correction_project P k hk (y+t•u) u (hc t ht)
      (h.c2 (k+1) (by omega) _ (hp _ (hseg t ht)))
    have ha' : ν.nrm (k+1) (L ((J P k (y+t•u) - hess P k (y+t•u)) u)) ≤ κ * ν.nrm k u := by
      change ν.nrm (k+1) ((J P (k+1) (proj P k (y+u))).inverse
        (proj P k ((J P k (y+t•u) - hess P k (y+t•u)) u))) ≤ _
      rw [hcorr]
      simp only [map_add,map_smul] at ⊢
      exact ha.trans (mul_le_mul_of_nonneg_left (ν.proj_le k u) hκ)
    have heq : L (hess P k (y+t•u) u - J P k y u) =
        -(L ((J P k (y+t•u) - hess P k (y+t•u)) u)) +
          L ((J P k (y+t•u) - J P k y) u) := by
      simp only [sub_apply,map_sub]
      abel
    rw [heq]
    exact (ν.triangle (k+1) _ _).trans (by rw [supplied_neg]; exact add_le_add ha' hb)
  have hr := supplied_ftc_residual_cross ν k (k+1)
    (fun t => grad P k x (y+t•u)) (fun t => hess P k (y+t•u) u) (J P k y u) L
    (grad_path_deriv_continuous P k y u hc) (fun t ht => grad_path_deriv P k x y u t (hc t ht))
    hz κ ω (ν.nrm k u) hb
  have hg := step_gradient_transition P k hk x y (h.c2 k hk.le _ hy)
    (h.c2 k hk.le _ he) (h.c2 (k+1) (by omega) _ (hp _ he)) (h.J_inv k hk.le _ hy)
  change ν.nrm (k+1) (-((J P (k+1) (proj P k (y+u))).inverse
    (grad P (k+1) (P.f k x (qL P k k (y+u))) (proj P k (y+u))))) ≤ _
  rw [supplied_neg,hg]
  simpa only [one_smul,L,ContinuousLinearMap.comp_apply] using hr


theorem rti_ball_estimate (P : OCP) (ν : CompatNorms P)
    (x0 : Vec P.nx) (y0 : PD P 0) (D0 : Set (PD P 0)) (κ ω : ℝ)
    (h : Thm41Hyp P ν x0 y0 D0 κ ω) (hκ : 0 ≤ κ) (k : ℕ) (hk : k < P.N)
    (hy : (rti P x0 y0 k).2 ∈ projTo P k '' ball0 P ν x0 y0 κ ω)
    (he : (rti P x0 y0 k).2 + rtiStep P x0 y0 k ∈ projTo P k '' ball0 P ν x0 y0 κ ω) :
    ν.nrm (k+1) (rtiStep P x0 y0 (k+1)) ≤
      delta P ν x0 y0 κ ω k * ν.nrm k (rtiStep P x0 y0 k) := by
  have hdom := projected_ball_domain ν x0 y0 D0 κ ω h k
  have hconv : Convex ℝ (projTo P k '' ball0 P ν x0 y0 κ ω) := by
    rw [show ball0 P ν x0 y0 κ ω = {z | ν.nrm 0 (z-y0) ≤
      ν.nrm 0 (rtiStep P x0 y0 0) / (1-delta P ν x0 y0 κ ω 0)} from rfl,
      projected_closedBall]
    exact supplied_ball_convex ν k _ _
  have hseg : ∀ t ∈ Icc (0 : ℝ) 1,
      (rti P x0 y0 k).2 + t • rtiStep P x0 y0 k ∈ Dset P D0 k := by
    intro t ht
    apply hdom
    have hh := hconv hy he (sub_nonneg.mpr ht.2) ht.1 (sub_add_cancel 1 t)
    convert hh using 1
    module
  have hh := native_projected_estimate P ν x0 y0 D0 κ ω h hκ k hk
    (rti P x0 y0 k).1 (rti P x0 y0 k).2 (hdom hy) (hdom he) hseg
  exact hh

end RealTimeIter.Contract.RTIFresh
end

-- RTIProof.NativeSigns

noncomputable section
namespace RealTimeIter.Contract.RTIFresh

theorem native_parameter_nonneg {P : OCP} (ν : CompatNorms P)
    (x0 : Vec P.nx) (y0 : PD P 0) (D0 : Set (PD P 0)) (κ ω : ℝ)
    (h : Thm41Hyp P ν x0 y0 D0 κ ω)
    (ha : 0 < ν.nrm 0 (rtiStep P x0 y0 0)) : 0 ≤ κ ∧ 0 ≤ ω := by
  let a := ν.nrm 0 (rtiStep P x0 y0 0)
  let R := a / (1 - delta P ν x0 y0 κ ω 0)
  have hR : 0 < R := div_pos ha (sub_pos.mpr h.h41d)
  let t := R / (2 * a)
  have ht : 0 < t := div_pos hR (by positivity)
  let z := y0 + t • rtiStep P x0 y0 0
  have hzlen : ν.nrm 0 (z - y0) = R / 2 := by
    dsimp only [z]
    rw [add_sub_cancel_left, ν.smul, abs_of_pos ht]
    change R / (2 * a) * a = R / 2
    have ha' : a ≠ 0 := ne_of_gt ha
    field_simp [ha']
  have hz : z ∈ Dset P D0 0 := by
    apply h.h41e
    change ν.nrm 0 (z - y0) ≤ R
    rw [hzlen]
    linarith
  have hy : y0 ∈ Dset P D0 0 := h.mem
  have hpos : 0 < ν.nrm 0 (z - y0) := by rw [hzlen]; positivity
  have hκ := h.h41a 0 (Nat.zero_le _) z hz y0 hy 0 (by norm_num)
    (by simpa using hy)
  have hω := h.h41b 0 (Nat.zero_le _) z hz y0 hy 1 (by norm_num)
    (by simpa using hz)
  have hnκ := supplied_nonneg ν 0
    ((J P 0 z).inverse ((J P 0 (y0 + (0 : ℝ) • (z - y0)) -
      hess P 0 (y0 + (0 : ℝ) • (z - y0))) (z - y0)))
  have hnω := supplied_nonneg ν 0
    ((J P 0 z).inverse ((J P 0 (y0 + (1 : ℝ) • (z - y0)) - J P 0 y0) (z - y0)))
  constructor
  · exact nonneg_of_mul_nonneg_left (hnκ.trans hκ) hpos
  · have hp : 0 < ν.nrm 0 (z - y0) ^ 2 := sq_pos_of_pos hpos
    exact nonneg_of_mul_nonneg_left (by simpa only [mul_one] using hnω.trans hω) hp

end RealTimeIter.Contract.RTIFresh
end

-- RTIProof.NativeConclusion

noncomputable section
namespace RealTimeIter.Contract.RTIFresh
theorem native_theorem_4_1 (P : OCP) (ν : CompatNorms P) (x0 : Vec P.nx) (y0 : PD P 0)
    (D0 : Set (PD P 0)) (κ ω : ℝ) (h : Thm41Hyp P ν x0 y0 D0 κ ω) :
    -- (4.2)
    (∀ k ≤ P.N, (rti P x0 y0 k).2 ∈ projTo P k '' ball0 P ν x0 y0 κ ω ∧
        projTo P k '' ball0 P ν x0 y0 κ ω ⊆ Dset P D0 k) ∧
    -- (4.3)
    (∀ k < P.N,
        ν.nrm (k + 1) (rtiStep P x0 y0 (k + 1))
          ≤ (κ + ω / 2 * ν.nrm k (rtiStep P x0 y0 k)) * ν.nrm k (rtiStep P x0 y0 k) ∧
        delta P ν x0 y0 κ ω k * ν.nrm k (rtiStep P x0 y0 k)
          ≤ delta P ν x0 y0 κ ω 0 * ν.nrm k (rtiStep P x0 y0 k) ∧
        delta P ν x0 y0 κ ω k ≤ delta P ν x0 y0 κ ω 0) ∧
    -- (4.4)
    (∀ k ≤ P.N, ∃ ystar : PD P k,
        Filter.Tendsto (newtonIter P k (rti P x0 y0 k).1 (rti P x0 y0 k).2) Filter.atTop
          (nhds ystar) ∧
        grad P k (rti P x0 y0 k).1 ystar = 0 ∧
        ν.nrm k ((rti P x0 y0 k).2 - ystar)
          ≤ ν.nrm k (rtiStep P x0 y0 k) / (1 - delta P ν x0 y0 κ ω k) ∧
        ν.nrm k (rtiStep P x0 y0 k) / (1 - delta P ν x0 y0 κ ω k)
          ≤ delta P ν x0 y0 κ ω 0 ^ k * ν.nrm 0 (rtiStep P x0 y0 0)
              / (1 - delta P ν x0 y0 κ ω 0))  := by
  by_cases hz : rtiStep P x0 y0 0 = 0
  · exact native_zero_branch P ν x0 y0 D0 κ ω h
      (fun k hk => (rti_zero_steps P ν x0 y0 D0 κ ω h hz k hk).2)
  · obtain ⟨hκ, hω⟩ := native_parameter_nonneg ν x0 y0 D0 κ ω h (supplied_pos ν 0 hz)
    exact native_positive_assembly P ν x0 y0 D0 κ ω h hκ hω
      (rti_ball_estimate P ν x0 y0 D0 κ ω h hκ)

end RealTimeIter.Contract.RTIFresh
end

-- RTIProof.FinalRoot

namespace RealTimeIter.Contract

theorem theorem_4_1 (P : OCP) (ν : CompatNorms P) (x0 : Vec P.nx) (y0 : PD P 0)
    (D0 : Set (PD P 0)) (κ ω : ℝ) (h : Thm41Hyp P ν x0 y0 D0 κ ω) :
    -- (4.2)
    (∀ k ≤ P.N, (rti P x0 y0 k).2 ∈ projTo P k '' ball0 P ν x0 y0 κ ω ∧
        projTo P k '' ball0 P ν x0 y0 κ ω ⊆ Dset P D0 k) ∧
    -- (4.3)
    (∀ k < P.N,
        ν.nrm (k + 1) (rtiStep P x0 y0 (k + 1))
          ≤ (κ + ω / 2 * ν.nrm k (rtiStep P x0 y0 k)) * ν.nrm k (rtiStep P x0 y0 k) ∧
        delta P ν x0 y0 κ ω k * ν.nrm k (rtiStep P x0 y0 k)
          ≤ delta P ν x0 y0 κ ω 0 * ν.nrm k (rtiStep P x0 y0 k) ∧
        delta P ν x0 y0 κ ω k ≤ delta P ν x0 y0 κ ω 0) ∧
    -- (4.4)
    (∀ k ≤ P.N, ∃ ystar : PD P k,
        Filter.Tendsto (newtonIter P k (rti P x0 y0 k).1 (rti P x0 y0 k).2) Filter.atTop
          (nhds ystar) ∧
        grad P k (rti P x0 y0 k).1 ystar = 0 ∧
        ν.nrm k ((rti P x0 y0 k).2 - ystar)
          ≤ ν.nrm k (rtiStep P x0 y0 k) / (1 - delta P ν x0 y0 κ ω k) ∧
        ν.nrm k (rtiStep P x0 y0 k) / (1 - delta P ν x0 y0 κ ω k)
          ≤ delta P ν x0 y0 κ ω 0 ^ k * ν.nrm 0 (rtiStep P x0 y0 0)
              / (1 - delta P ν x0 y0 κ ω 0)) := by
  exact RTIFresh.native_theorem_4_1 P ν x0 y0 D0 κ ω h

end RealTimeIter.Contract

open RealTimeIter.Contract in
theorem solution (P : OCP) (ν : CompatNorms P) (x0 : Vec P.nx) (y0 : PD P 0)
    (D0 : Set (PD P 0)) (κ ω : ℝ) (h : Thm41Hyp P ν x0 y0 D0 κ ω) :
    -- (4.2)
    (∀ k ≤ P.N, (rti P x0 y0 k).2 ∈ projTo P k '' ball0 P ν x0 y0 κ ω ∧
        projTo P k '' ball0 P ν x0 y0 κ ω ⊆ Dset P D0 k) ∧
    -- (4.3)
    (∀ k < P.N,
        ν.nrm (k + 1) (rtiStep P x0 y0 (k + 1))
          ≤ (κ + ω / 2 * ν.nrm k (rtiStep P x0 y0 k)) * ν.nrm k (rtiStep P x0 y0 k) ∧
        delta P ν x0 y0 κ ω k * ν.nrm k (rtiStep P x0 y0 k)
          ≤ delta P ν x0 y0 κ ω 0 * ν.nrm k (rtiStep P x0 y0 k) ∧
        delta P ν x0 y0 κ ω k ≤ delta P ν x0 y0 κ ω 0) ∧
    -- (4.4)
    (∀ k ≤ P.N, ∃ ystar : PD P k,
        Filter.Tendsto (newtonIter P k (rti P x0 y0 k).1 (rti P x0 y0 k).2) Filter.atTop
          (nhds ystar) ∧
        grad P k (rti P x0 y0 k).1 ystar = 0 ∧
        ν.nrm k ((rti P x0 y0 k).2 - ystar)
          ≤ ν.nrm k (rtiStep P x0 y0 k) / (1 - delta P ν x0 y0 κ ω k) ∧
        ν.nrm k (rtiStep P x0 y0 k) / (1 - delta P ν x0 y0 κ ω k)
          ≤ delta P ν x0 y0 κ ω 0 ^ k * ν.nrm 0 (rtiStep P x0 y0 0)
              / (1 - delta P ν x0 y0 κ ω 0))  := by
  exact RealTimeIter.Contract.theorem_4_1 P ν x0 y0 D0 κ ω h
