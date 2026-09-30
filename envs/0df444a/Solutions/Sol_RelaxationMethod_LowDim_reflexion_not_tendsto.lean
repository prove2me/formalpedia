-- Prove2me | solution 1 for RelaxationMethod.LowDim.reflexion_not_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T08:40:04.099626+00:00
-- url     : https://prove2.me/submissions/3cf3dc23-69bb-4603-bf50-ef8bca16e9a9

import Definitions.Def_RelaxationMethod_LowDim_RelaxStep
import Mathlib.Order.Filter.Finite
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


open Filter
open scoped Topology
private theorem limit_feasible {n m : ℕ} (a : Fin m → EuclideanSpace ℝ (Fin n)) (b : Fin m → ℝ)
    (hA : (polytope a b).Nonempty) (lam : ℝ) (hlam0 : 0 < lam)
    (p : ℕ → EuclideanSpace ℝ (Fin n)) (hrun : IsRelaxRun a b lam p)
    (hinf : ∀ ν : ℕ, p ν ∉ polytope a b) (l : EuclideanSpace ℝ (Fin n))
    (hl : Tendsto p atTop (𝓝 l)) : l ∈ polytope a b ∧ l ∈ frontier (polytope a b) := by
  have hlA : l ∈ polytope a b := by
    apply Set.mem_iInter.mpr
    intro i
    have hs (ν : ℕ) : lam * Metric.infDist (p ν) (halfSpace (a i) (b i)) ≤ dist (p ν) (p (ν+1)) := by
      obtain ⟨j,hfar,q,hq,hpq,hnext⟩  := hrun ν (hinf ν)
      rw [hnext]
      have he : dist (p ν) (p ν+lam • (q-p ν)) = lam*dist (p ν) q := by
        have hv : p ν-(p ν+lam • (q-p ν)) = lam • (p ν-q) := by module
        simp only [dist_eq_norm]
        rw [hv,norm_smul,Real.norm_eq_abs,abs_of_pos hlam0]
      rw [he,hpq]
      exact mul_le_mul_of_nonneg_left (hfar i) hlam0.le
    have hshift : Tendsto (fun ν : ℕ => p (ν+1)) atTop (𝓝 l) := hl.comp (tendsto_add_atTop_nat 1)
    have hstep : Tendsto (fun ν => dist (p ν) (p (ν+1))) atTop (𝓝 0) := by simpa using hl.dist hshift
    have hdist : Tendsto (fun ν => lam * Metric.infDist (p ν) (halfSpace (a i) (b i))) atTop
        (𝓝 (lam * Metric.infDist l (halfSpace (a i) (b i)))) :=
      tendsto_const_nhds.mul ((Metric.continuous_infDist_pt _).tendsto l |>.comp hl)
    have hle := le_of_tendsto_of_tendsto hdist hstep (Filter.Eventually.of_forall hs)
    have hne : (halfSpace (a i) (b i)).Nonempty := by
      obtain ⟨x,hx⟩ := hA
      exact ⟨x,Set.mem_iInter.mp hx i⟩
    by_contra hnot
    have hpos := (half_closed (a i) (b i)).notMem_iff_infDist_pos hne |>.mp hnot
    have hmul := mul_pos hlam0 hpos
    linarith
  refine ⟨hlA,?_⟩
  rw [frontier_eq_closure_inter_closure]
  refine ⟨subset_closure hlA,?_⟩
  exact isClosed_closure.mem_of_tendsto hl (Filter.Eventually.of_forall (fun ν => subset_closure (hinf ν)))


theorem solution {n m : ℕ} (a : Fin m → EuclideanSpace ℝ (Fin n)) (b : Fin m → ℝ)
    (hA : (RelaxationMethod.LowDim.polytope a b).Nonempty) (p : ℕ → EuclideanSpace ℝ (Fin n))
    (hrun : ∀ ν, p ν ∉ RelaxationMethod.LowDim.polytope a b → RelaxationMethod.LowDim.IsRelaxStep a b 2 (p ν) (p (ν + 1)))
    (hinf : ∀ ν, p ν ∉ RelaxationMethod.LowDim.polytope a b) :
    ¬ ∃ l, Tendsto p atTop (𝓝 l) := by
  rintro ⟨l,hl⟩
  have hrunFull : IsRelaxRun a b 2 p := hrun
  have hinfFull : ∀ ν, p ν ∉ polytope a b := hinf
  have hlA : l ∈ polytope a b := (limit_feasible a b hA 2 (by norm_num) p hrun hinf l hl).1
  have he (i : Fin m) : ∀ᶠ ν in atTop, inner ℝ (a i) l+b i ≠ 0 → p ν ∈ halfSpace (a i) (b i) := by
    by_cases hz : inner ℝ (a i) l+b i=0
    · exact Filter.Eventually.of_forall (fun ν hne => False.elim (hne hz))
    · have hpos : 0 < inner ℝ (a i) l+b i := lt_of_le_of_ne (Set.mem_iInter.mp hlA i) (fun hzero => hz hzero.symm)
      have hc : Tendsto (fun ν => inner ℝ (a i) (p ν)+b i) atTop (𝓝 (inner ℝ (a i) l+b i)) :=
        ((continuous_const.inner continuous_id).add continuous_const).tendsto l |>.comp hl
      have hgt := (tendsto_order.mp hc).1 0 hpos
      filter_upwards [hgt] with ν hν
      intro _
      exact hν.le
  obtain ⟨N,hN⟩ := eventually_atTop.mp (eventually_all.mpr he)
  have hs (ν : ℕ) (hν : N ≤ ν) : dist (p (ν+1)) l = dist (p ν) l := by
    obtain ⟨j,hfar,q,hq,hpq,hnext⟩  := hrunFull ν (hinfFull ν)
    have hex : ∃ i, p ν ∉ halfSpace (a i) (b i) := by
      simpa only [polytope,Set.mem_iInter,not_forall] using hinfFull ν
    obtain ⟨i,hi⟩ := hex
    have hne : (halfSpace (a i) (b i)).Nonempty := by
      obtain ⟨x,hx⟩ := hA
      exact ⟨x,Set.mem_iInter.mp hx i⟩
    have hpos := ((half_closed (a i) (b i)).notMem_iff_infDist_pos hne |>.mp hi).trans_le (hfar i)
    have hpj : p ν ∉ halfSpace (a j) (b j) := by
      intro hmem
      rw [Metric.infDist_zero_of_mem hmem] at hpos
      exact (lt_irrefl 0) hpos
    have hboundary : inner ℝ (a j) l+b j=0 := by
      by_contra hnot
      exact hpj (hN ν hν j hnot)
    rw [hnext]
    exact (reflection_eq_iff (a j) (p ν) q l (b j) hpj hq hpq).mpr hboundary
  have hc (ν : ℕ) (hν : N ≤ ν) : dist (p ν) l = dist (p N) l := by
    induction ν,hν using Nat.le_induction with
    | base => rfl
    | succ ν hν ih => rw [hs ν hν,ih]
  have hconst : Tendsto (fun ν => dist (p ν) l) atTop (𝓝 (dist (p N) l)) := by
    apply tendsto_const_nhds.congr'
    exact eventually_atTop.mpr ⟨N,fun ν hν => (hc ν hν).symm⟩
  have hz : Tendsto (fun ν => dist (p ν) l) atTop (𝓝 0) := by simpa using hl.dist (tendsto_const_nhds : Tendsto (fun _ : ℕ => l) atTop (𝓝 l))
  have hdist : dist (p N) l=0 := tendsto_nhds_unique hconst hz
  have hpNl : p N=l := dist_eq_zero.mp hdist
  apply hinf N
  rw [hpNl]
  exact hlA
