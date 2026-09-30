-- Prove2me | solution 1 for RelaxationMethod.FullDim.step_pointwise_closer
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T08:32:32.466089+00:00
-- url     : https://prove2.me/submissions/c8d80827-94d8-4a8c-9078-51b929062c33

import Definitions.Def_RelaxationMethod_FullDim_RelaxStep
import Definitions.Def_RelaxationMethod_FullDim_FejerMonotone
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Tactic
set_option autoImplicit false
open RelaxationMethod.FullDim
open scoped InnerProductSpace

private theorem half_closed {n : ℕ} (u : EuclideanSpace ℝ (Fin n)) (b : ℝ) : IsClosed (halfSpace u b) :=
  isClosed_le continuous_const ((continuous_const.inner continuous_id).add continuous_const)

private theorem half_convex {n : ℕ} (u : EuclideanSpace ℝ (Fin n)) (b : ℝ) : Convex ℝ (halfSpace u b) := by
  intro x hx y hy a c ha hc hac
  change 0 ≤ inner ℝ u (a • x+c • y)+b
  change 0 ≤ inner ℝ u x+b at hx
  change 0 ≤ inner ℝ u y+b at hy
  simp only [inner_add_right,real_inner_smul_right]
  nlinarith [mul_nonneg ha hx,mul_nonneg hc hy,congrArg (fun t : ℝ => t*b) hac]

private theorem nearest_inner_metric {n : ℕ} (S : Set (EuclideanSpace ℝ (Fin n)))
    (hcv : Convex ℝ S) (p q : EuclideanSpace ℝ (Fin n)) (hq : q ∈ S)
    (hpq : dist p q = Metric.infDist p S) : ∀ x ∈ S, inner ℝ (p-q) (x-q) ≤ 0 := by
  letI : Nonempty S := ⟨⟨q,hq⟩⟩
  have hb : BddBelow (Set.range (fun y : S => ‖p-y‖)) := ⟨0, by rintro _ ⟨y,rfl⟩; exact norm_nonneg _⟩
  apply (norm_eq_iInf_iff_real_inner_le_zero hcv hq).mp
  apply le_antisymm
  · apply le_ciInf
    intro y
    simpa only [dist_eq_norm] using hpq.trans_le (Metric.infDist_le_dist_of_mem y.2)
  · exact ciInf_le hb ⟨q,hq⟩

private theorem relax_dist {n : ℕ} (S : Set (EuclideanSpace ℝ (Fin n)))
    (hcv : Convex ℝ S) (p q x : EuclideanSpace ℝ (Fin n)) (hq : q ∈ S) (hx : x ∈ S)
    (hpq : dist p q = Metric.infDist p S) (lam : ℝ) (hlam0 : 0 < lam) (hlam2 : lam ≤ 2) :
    dist (p+lam • (q-p)) x ≤ dist p x := by
  have hi := nearest_inner_metric S hcv p q hq hpq x hx
  have he : inner ℝ (p-q) (x-q) = inner ℝ (p-x) (q-p)+inner ℝ (q-p) (q-p) := by
    simp only [inner_sub_left,inner_sub_right,real_inner_comm x p,real_inner_comm x q,real_inner_comm q p]
    ring
  rw [he,real_inner_self_eq_norm_sq] at hi
  have hex : ‖(p-x)+lam • (q-p)‖^2 = ‖p-x‖^2 + 2*lam*inner ℝ (p-x) (q-p) + lam^2*‖q-p‖^2 := by
    simp only [norm_add_sq_real,real_inner_smul_right,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs]
    ring
  have hw := mul_le_mul_of_nonneg_left hi (by positivity : 0 ≤ 2*lam)
  have hl : lam^2-2*lam ≤ 0 := by nlinarith
  have hn := mul_nonpos_of_nonpos_of_nonneg hl (sq_nonneg ‖q-p‖)
  rw [dist_eq_norm,dist_eq_norm]
  have hid : p+lam • (q-p)-x = (p-x)+lam • (q-p) := by abel
  rw [hid]
  nlinarith [norm_nonneg ((p-x)+lam • (q-p)),norm_nonneg (p-x)]

private theorem relax_distinct {n : ℕ} (p q : EuclideanSpace ℝ (Fin n)) (hpq : p ≠ q)
    (lam : ℝ) (hlam : 0 < lam) : p ≠ p+lam • (q-p) := by
  intro he
  have he' : p+lam • (q-p)=p+0 := by simpa using he.symm
  have hs := add_left_cancel he'
  have hzero : q-p=0 := (smul_eq_zero.mp hs).resolve_left (ne_of_gt hlam)
  exact hpq (sub_eq_zero.mp hzero).symm

private theorem relax_strict {n : ℕ} (S : Set (EuclideanSpace ℝ (Fin n)))
    (hcv : Convex ℝ S) (p q x : EuclideanSpace ℝ (Fin n)) (hq : q ∈ S) (hx : x ∈ S)
    (hpq : dist p q = Metric.infDist p S) (lam : ℝ) (hlam0 : 0 < lam) (hlam2 : lam < 2) (hne : p ≠ q) :
    dist (p+lam • (q-p)) x < dist p x := by
  have hi := nearest_inner_metric S hcv p q hq hpq x hx
  have he : inner ℝ (p-q) (x-q) = inner ℝ (p-x) (q-p)+inner ℝ (q-p) (q-p) := by
    simp only [inner_sub_left,inner_sub_right,real_inner_comm x p,real_inner_comm x q,real_inner_comm q p]
    ring
  rw [he,real_inner_self_eq_norm_sq] at hi
  have hex : ‖(p-x)+lam • (q-p)‖^2 = ‖p-x‖^2 + 2*lam*inner ℝ (p-x) (q-p) + lam^2*‖q-p‖^2 := by
    simp only [norm_add_sq_real,real_inner_smul_right,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs]
    ring
  have hw := mul_le_mul_of_nonneg_left hi (by positivity : 0 ≤ 2*lam)
  have hl : lam^2-2*lam < 0 := by nlinarith
  have hn := mul_neg_of_neg_of_pos hl (sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hne.symm)))
  rw [dist_eq_norm,dist_eq_norm]
  have hid : p+lam • (q-p)-x = (p-x)+lam • (q-p) := by abel
  rw [hid]
  nlinarith [norm_nonneg ((p-x)+lam • (q-p)),norm_nonneg (p-x)]


private theorem half_projection {n : ℕ} (u p q : EuclideanSpace ℝ (Fin n)) (b : ℝ)
    (hp : p ∉ halfSpace u b) (hq : q ∈ halfSpace u b)
    (hpq : dist p q = Metric.infDist p (halfSpace u b)) :
    ∃ t : ℝ, 0 < t ∧ q=p+t • u ∧ t*‖u‖^2=-(inner ℝ u p+b) := by
  have hneg : inner ℝ u p+b < 0 := lt_of_not_ge hp
  have hu : u ≠ 0 := by
    intro he
    have hb : 0 ≤ b := by simpa [halfSpace,he] using hq
    have hb' : b < 0 := by simpa [he] using hneg
    linarith
  have hn : 0 < ‖u‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hu)
  let t := -(inner ℝ u p+b)/‖u‖^2
  have ht : 0 < t := div_pos (neg_pos.mpr hneg) hn
  have hrel : t*‖u‖^2=-(inner ℝ u p+b) := div_mul_cancel₀ _ hn.ne'
  let r := p+t • u
  have hr0 : inner ℝ u r+b=0 := by
    dsimp [r]
    rw [inner_add_right,real_inner_smul_right,real_inner_self_eq_norm_sq]
    linarith
  have hr : r ∈ halfSpace u b := by change 0 ≤ inner ℝ u r+b; rw [hr0]
  have hri (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ halfSpace u b) : inner ℝ (p-r) (x-r) ≤ 0 := by
    have he : p-r = -t • u := by dsimp [r]; module
    have hr' : inner ℝ u r = -b := by linarith
    rw [he,real_inner_smul_left,inner_sub_right,hr']
    change 0 ≤ inner ℝ u x+b at hx
    nlinarith [mul_nonneg ht.le hx]
  have h1 := nearest_inner_metric _ (half_convex u b) p q hq hpq r hr
  have h2 := hri q hq
  have hh : inner ℝ (q-r) (q-r) ≤ 0 := by
    simp only [inner_sub_left,inner_sub_right,real_inner_comm r q] at *
    linarith
  have hqr : q=r := by
    rw [real_inner_self_eq_norm_sq] at hh
    have hz : ‖q-r‖=0 := by nlinarith [norm_nonneg (q-r)]
    exact sub_eq_zero.mp (norm_eq_zero.mp hz)
  exact ⟨t,ht,hqr,hrel⟩

private theorem reflection_eq_iff {n : ℕ} (u p q x : EuclideanSpace ℝ (Fin n)) (b : ℝ)
    (hp : p ∉ halfSpace u b) (hq : q ∈ halfSpace u b)
    (hpq : dist p q = Metric.infDist p (halfSpace u b)) :
    dist (p+(2 : ℝ) • (q-p)) x = dist p x ↔ inner ℝ u x+b=0 := by
  obtain ⟨t,ht,hqr,hrel⟩ := half_projection u p q b hp hq hpq
  have hvec : p+(2 : ℝ) • (q-p)-x = (p-x)+(2*t) • u := by rw [hqr]; module
  have hcomm : inner ℝ (p-x) u = inner ℝ u p-inner ℝ u x := by
    rw [inner_sub_left]
    congr 1 <;> exact real_inner_comm _ _
  have he : dist (p+(2 : ℝ) • (q-p)) x ^ 2 = dist p x ^ 2 - 4*t*(inner ℝ u x+b) := by
    rw [dist_eq_norm,dist_eq_norm,hvec,norm_add_sq_real,real_inner_smul_right,hcomm]
    simp only [norm_smul,Real.norm_eq_abs,mul_pow,sq_abs]
    nlinarith [congrArg (fun z : ℝ => 4*t*z) hrel]
  constructor
  · intro hd
    have hz : 4*t*(inner ℝ u x+b)=0 := by rw [hd] at he; linarith
    exact (mul_eq_zero.mp hz).resolve_left (by positivity)
  · intro hx
    rw [hx,mul_zero,sub_zero] at he
    nlinarith [dist_nonneg (x := p+(2 : ℝ) • (q-p)) (y := x),dist_nonneg (x := p) (y := x)]

theorem solution {n m : ℕ} (a : Fin m → EuclideanSpace ℝ (Fin n)) (b : Fin m → ℝ)
    (hA : (polytope a b).Nonempty) (lam : ℝ) (hlam0 : 0 < lam) (hlam2 : lam ≤ 2)
    (p q : EuclideanSpace ℝ (Fin n)) (j : Fin m) (hpj : p ∉ halfSpace (a j) (b j))
    (hq : q ∈ halfSpace (a j) (b j))
    (hpq : dist p q = Metric.infDist p (halfSpace (a j) (b j))) :
    p + lam • (q - p) ≠ p ∧
      (∀ x ∈ polytope a b, dist (p + lam • (q - p)) x ≤ dist p x) ∧
      (lam < 2 → IsPointwiseCloser (polytope a b) p (p + lam • (q - p))) ∧
      (lam = 2 → ∀ x ∈ polytope a b,
        (dist (p + lam • (q - p)) x = dist p x ↔ inner ℝ (a j) x + b j = 0))  := by
  have hne : p ≠ q := by intro he; apply hpj; simpa [he] using hq
  refine ⟨(relax_distinct p q hne lam hlam0).symm,?_,?_,?_⟩
  · intro x hx
    exact relax_dist _ (half_convex (a j) (b j)) p q x hq (Set.mem_iInter.mp hx j) hpq lam hlam0 hlam2
  · intro hlt x hx
    exact relax_strict _ (half_convex (a j) (b j)) p q x hq (Set.mem_iInter.mp hx j) hpq lam hlam0 hlt hne
  · intro he x hx
    subst lam
    exact reflection_eq_iff (a j) p q x (b j) hpj hq hpq
