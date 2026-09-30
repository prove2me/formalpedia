-- Prove2me | solution 1 for RelaxationMethod.LowDim.step_length_pos
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T08:43:51.648867+00:00
-- url     : https://prove2.me/submissions/6061344a-0fd9-432a-9fbe-7b520375a7f1

import Definitions.Def_RelaxationMethod_LowDim_RelaxStep
import Mathlib.Topology.Sequences
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecificLimits.Basic
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

private theorem one_step {n m : ℕ} (a : Fin m → EuclideanSpace ℝ (Fin n)) (b : Fin m → ℝ)
    (hA : (polytope a b).Nonempty) (lam : ℝ) (hlam0 : 0 < lam) (hlam2 : lam ≤ 2)
    (p p' : EuclideanSpace ℝ (Fin n)) (hstep : IsRelaxStep a b lam p p') (hp : p ∉ polytope a b) :
    p ≠ p' ∧ ∀ x ∈ polytope a b, dist p' x ≤ dist p x := by
  obtain ⟨j,hfar,q,hq,hpq,rfl⟩ := hstep
  have hex : ∃ i, p ∉ halfSpace (a i) (b i) := by simpa only [polytope,Set.mem_iInter,not_forall] using hp
  obtain ⟨i,hi⟩ := hex
  have hne : (halfSpace (a i) (b i)).Nonempty := by
    obtain ⟨x,hx⟩ := hA
    exact ⟨x,Set.mem_iInter.mp hx i⟩
  have hpos := (half_closed (a i) (b i)).notMem_iff_infDist_pos hne |>.mp hi
  have hdist : 0 < dist p q := by rw [hpq]; exact hpos.trans_le (hfar i)
  refine ⟨relax_distinct p q (dist_pos.mp hdist) lam hlam0,?_⟩
  intro x hx
  exact relax_dist _ (half_convex (a j) (b j)) p q x hq (Set.mem_iInter.mp hx j) hpq lam hlam0 hlam2

private theorem run_fejer {n m : ℕ} (a : Fin m → EuclideanSpace ℝ (Fin n)) (b : Fin m → ℝ)
    (hA : (polytope a b).Nonempty) (lam : ℝ) (hlam0 : 0 < lam) (hlam2 : lam ≤ 2)
    (p : ℕ → EuclideanSpace ℝ (Fin n)) (hrun : IsRelaxRun a b lam p)
    (hinf : ∀ ν : ℕ, p ν ∉ polytope a b) : IsFejerMonotone (polytope a b) p := by
  have hs (ν : ℕ) := one_step a b hA lam hlam0 hlam2 (p ν) (p (ν+1)) (hrun ν (hinf ν)) (hinf ν)
  exact ⟨hinf,fun ν => (hs ν).1,fun x hx ν => (hs ν).2 x hx⟩


open Filter
open scoped Topology
private theorem fejer_tendsto_of_cluster {E : Type*} [PseudoMetricSpace E]
    (p : ℕ → E) (l : E) (hmono : ∀ n, dist (p (n+1)) l ≤ dist (p n) l)
    (u : ℕ → ℕ) (hu : Tendsto (fun n => p (u n)) atTop (𝓝 l)) :
    Tendsto p atTop (𝓝 l) := by
  have ha : Antitone (fun n => dist (p n) l) := antitone_nat_of_succ_le hmono
  rw [Metric.tendsto_atTop] at hu ⊢
  intro ε hε
  obtain ⟨N,hN⟩ := hu ε hε
  refine ⟨u N,?_⟩
  intro n hn
  exact (ha hn).trans_lt (hN N le_rfl)

private theorem half_distance_bound {n m : ℕ} (a : Fin m → EuclideanSpace ℝ (Fin n)) (b : Fin m → ℝ)
    (lam : ℝ) (hlam : 0 < lam) (p p' : EuclideanSpace ℝ (Fin n))
    (hstep : IsRelaxStep a b lam p p') (i : Fin m) :
    lam*Metric.infDist p (halfSpace (a i) (b i)) ≤ dist p' p := by
  obtain ⟨j,hfar,q,hq,hpq,rfl⟩ := hstep
  have he : dist (p+lam • (q-p)) p = lam*dist p q := by
    have hv : p+lam • (q-p)-p = lam • (q-p) := by abel
    simp only [dist_eq_norm]
    rw [hv,norm_smul,Real.norm_eq_abs,abs_of_pos hlam,norm_sub_rev q p]
  rw [he,hpq]
  exact mul_le_mul_of_nonneg_left (hfar i) hlam.le

theorem solution {n m : ℕ} (a : Fin m → EuclideanSpace ℝ (Fin n)) (b : Fin m → ℝ)
    (hA : (RelaxationMethod.LowDim.polytope a b).Nonempty) (hr : affineSpan ℝ (RelaxationMethod.LowDim.polytope a b) ≠ ⊤)
    (lam : ℝ) (hlam0 : 0 < lam) (hlam2 : lam ≤ 2)
    (p : ℕ → EuclideanSpace ℝ (Fin n))
    (hrun : ∀ ν, p ν ∉ RelaxationMethod.LowDim.polytope a b → RelaxationMethod.LowDim.IsRelaxStep a b lam (p ν) (p (ν + 1)))
    (hinf : ∀ ν, p ν ∉ RelaxationMethod.LowDim.polytope a b) (hdiv : ¬ ∃ l, Tendsto p atTop (𝓝 l)) :
    ∃ c : ℝ, 0 < c ∧ ∀ ν, c ≤ dist (p (ν + 1)) (p ν) := by
  by_contra hnone
  push_neg at hnone
  have hrunFull : IsRelaxRun a b lam p := hrun
  have hinfFull : ∀ ν, p ν ∉ polytope a b := hinf
  have hfejer := run_fejer a b hA lam hlam0 hlam2 p hrunFull hinfFull
  have hex (k : ℕ) : ∃ ν, dist (p (ν+1)) (p ν) < 1/((k:ℝ)+1) := hnone _ (by positivity)
  choose idx hidx using hex
  have hsmall : Tendsto (fun k => dist (p (idx k+1)) (p (idx k))) atTop (𝓝 0) :=
    squeeze_zero (fun k => dist_nonneg) (fun k => (hidx k).le) tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨x,hx⟩ := hA
  have hanti : Antitone (fun ν => dist (p ν) x) := antitone_nat_of_succ_le (fun ν => hfejer.2.2 x hx ν)
  have hbounded (k : ℕ) : p (idx k) ∈ Metric.closedBall x (dist (p 0) x) :=
    hanti (Nat.zero_le (idx k))
  obtain ⟨l,hlball,φ,hφ,hsub⟩ := (isCompact_closedBall x (dist (p 0) x)).tendsto_subseq hbounded
  have hsubl : Tendsto (fun k => p (idx (φ k))) atTop (𝓝 l) := hsub
  have hsubsmall : Tendsto (fun k => dist (p (idx (φ k)+1)) (p (idx (φ k)))) atTop (𝓝 0) :=
    hsmall.comp hφ.tendsto_atTop
  have hlA : l ∈ polytope a b := by
    apply Set.mem_iInter.mpr
    intro i
    have hs (k : ℕ) := half_distance_bound a b lam hlam0 (p (idx (φ k))) (p (idx (φ k)+1))
      (hrunFull _ (hinfFull _)) i
    have hdist : Tendsto (fun k => lam*Metric.infDist (p (idx (φ k))) (halfSpace (a i) (b i))) atTop
        (𝓝 (lam*Metric.infDist l (halfSpace (a i) (b i)))) :=
      tendsto_const_nhds.mul ((Metric.continuous_infDist_pt _).tendsto l |>.comp hsubl)
    have hle := le_of_tendsto_of_tendsto hdist hsubsmall (Filter.Eventually.of_forall hs)
    have hne : (halfSpace (a i) (b i)).Nonempty := ⟨x,Set.mem_iInter.mp hx i⟩
    by_contra hnot
    have hpos := (half_closed (a i) (b i)).notMem_iff_infDist_pos hne |>.mp hnot
    have hmul := mul_pos hlam0 hpos
    linarith
  apply hdiv
  refine ⟨l,?_⟩
  exact fejer_tendsto_of_cluster p l (fun ν => hfejer.2.2 l hlA ν) (fun k => idx (φ k)) hsubl
