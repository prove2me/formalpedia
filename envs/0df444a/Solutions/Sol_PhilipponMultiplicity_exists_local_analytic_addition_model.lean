-- Prove2me | solution 1 for PhilipponMultiplicity.exists_local_analytic_addition_model
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-03T08:25:44.912403+00:00
-- url     : https://prove2.me/submissions/a997ee55-d170-417e-ba8b-03dafbf44818

import Theorems.Thm_PhilipponMultiplicity_exists_normalized_analytic_group_chart
import Definitions.Def_PhilipponMultiplicity_Geometry
import Mathlib.Analysis.Analytic.Polynomial

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Topology
open Filter MvPolynomial

namespace PhilipponMultiplicity

theorem MultiProjectiveSpace.eval_block_scale {K : Type*} [Field K]
    (M : MultiProjectiveSpace K) (P : M.CoordinateRing)
    (D : M.FactorIndex → ℕ) (hP : M.IsHomogeneous P D)
    (v : M.Variable → K) (a : M.FactorIndex → K) :
    MvPolynomial.eval (fun j => a j.1 * v j) P = (∏ i, a i ^ D i) * MvPolynomial.eval v P := by
  classical
  rw [eval_eq', eval_eq', Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  have hscale : (∏ j : M.Variable, a j.1 ^ d j) = ∏ i, a i ^ D i := by
    rw [Fintype.prod_sigma]
    apply Finset.prod_congr rfl
    intro i _
    change (∏ j : Fin (M.ambientDimension i + 1), a i ^ d ⟨i, j⟩) = a i ^ D i
    rw [Finset.prod_pow_eq_pow_sum, hP d hd i]
  simp only [mul_pow, Finset.prod_mul_distrib, hscale]
  ring


end PhilipponMultiplicity
end

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Topology
open MvPolynomial

namespace PhilipponMultiplicity

theorem MultiProjectiveSpace.eval_eq_zero_iff_of_lift
    {K : Type*} [Field K] (M : MultiProjectiveSpace K) (p : M.Point)
    (v : M.Variable → K)
    (hv : ∀ i, ∃ h : (fun j => v ⟨i, j⟩) ≠ 0,
      Projectivization.mk K (fun j => v ⟨i, j⟩) h = p i)
    (P : M.CoordinateRing) (D : M.FactorIndex → ℕ) (hP : M.IsHomogeneous P D) :
    MvPolynomial.eval v P = 0 ↔ M.eval P p = 0 := by
  classical
  have ha (i : M.FactorIndex) : ∃ a : Kˣ,
      ∀ j, v ⟨i, j⟩ = (a : K) * (p i).rep j := by
    obtain ⟨h, he⟩ := hv i
    obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff K _ _ h
      (Projectivization.rep_nonzero (p i))).mp
      (he.trans (Projectivization.mk_rep (p i)).symm)
    refine ⟨a, fun j => ?_⟩
    simpa only [Pi.smul_apply, Units.smul_def, smul_eq_mul] using (congrFun ha j).symm
  choose a ha using ha
  have hv' : v = fun j => (a j.1 : K) * M.coordinate p j := by
    funext j
    exact ha j.1 j.2
  have hne : (∏ i, (a i : K) ^ D i) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun i _ => pow_ne_zero _ (a i).ne_zero)
  rw [hv', M.eval_block_scale P D hP (M.coordinate p) (fun i => (a i : K))]
  exact mul_eq_zero.trans (or_iff_right hne)


end PhilipponMultiplicity
end

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
open Set MvPolynomial
open scoped BigOperators Topology

namespace PhilipponMultiplicity.MultiProjectiveSpace
universe u
variable {K : Type u} [Field K]

theorem homogeneous_tuple_lift {ι : Type*} (M : MultiProjectiveSpace K)
    (p : M.Point) (v : M.Variable → K)
    (hv : ∀ i, ∃ h : (fun j => v ⟨i, j⟩) ≠ 0,
      Projectivization.mk K (fun j => v ⟨i, j⟩) h = p i)
    (P : ι → M.CoordinateRing) (D : M.FactorIndex → ℕ)
    (hP : ∀ j, M.IsHomogeneous (P j) D)
    (hn : (fun j => M.eval (P j) p) ≠ 0) :
    ∃ h : (fun j => MvPolynomial.eval v (P j)) ≠ 0,
      Projectivization.mk K (fun j => MvPolynomial.eval v (P j)) h =
        Projectivization.mk K (fun j => M.eval (P j) p) hn := by
  classical
  have ha (i : M.FactorIndex) : ∃ a : Kˣ,
      ∀ j, v ⟨i, j⟩ = (a : K) * (p i).rep j := by
    obtain ⟨h, he⟩ := hv i
    obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff K _ _ h
      (Projectivization.rep_nonzero (p i))).mp
      (he.trans (Projectivization.mk_rep (p i)).symm)
    refine ⟨a, fun j => ?_⟩
    simpa only [Pi.smul_apply, Units.smul_def, smul_eq_mul] using (congrFun ha j).symm
  choose a ha using ha
  have hv' : v = fun j => (a j.1 : K) * M.coordinate p j := by
    funext j
    exact ha j.1 j.2
  let b : K := ∏ i, (a i : K) ^ D i
  have hb : b ≠ 0 := Finset.prod_ne_zero_iff.mpr
    (fun i _ => pow_ne_zero _ (a i).ne_zero)
  have heval : (fun j => MvPolynomial.eval v (P j)) = b • (fun j => M.eval (P j) p) := by
    funext j
    rw [hv', M.eval_block_scale (P j) D (hP j) (M.coordinate p) (fun i => (a i : K))]
    rfl
  have hn' : (fun j => MvPolynomial.eval v (P j)) ≠ 0 := by
    rw [heval]
    exact smul_ne_zero hb hn
  exact ⟨hn', (Projectivization.mk_eq_mk_iff' K _ _ _ _).mpr ⟨b, heval.symm⟩⟩


end PhilipponMultiplicity.MultiProjectiveSpace
end

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open Filter MvPolynomial
open scoped Topology BigOperators

namespace PhilipponMultiplicity.AnalyticRegularMaps
universe u

theorem normalized_lifts_eq {K ι : Type*} [Field K]
    {v w : ι → K} {hv : v ≠ 0} {hw : w ≠ 0}
    (he : Projectivization.mk K v hv = Projectivization.mk K w hw)
    (c : ι) (hc : v c = 1) (hc' : w c = 1) : v = w := by
  obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff K v w hv hw).mp he
  have ha1 : (a : K) = 1 := by
    have h := congrFun ha c
    simpa only [Pi.smul_apply, Units.smul_def, smul_eq_mul, hc, hc', mul_one] using h
  funext j
  have h := congrFun ha j
  simpa only [Pi.smul_apply, Units.smul_def, smul_eq_mul, ha1, one_mul] using h.symm

theorem pivot_ne_zero {K ι : Type*} [Field K]
    {v w : ι → K} {hv : v ≠ 0} {hw : w ≠ 0}
    (he : Projectivization.mk K v hv = Projectivization.mk K w hw)
    (c : ι) (hc : w c = 1) : v c ≠ 0 := by
  obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff K v w hv hw).mp he
  have h := congrFun ha c
  have h' : v c = (a : K) := by
    simpa only [Pi.smul_apply, Units.smul_def, smul_eq_mul, hc, mul_one] using h.symm
  exact h'.trans_ne a.ne_zero

theorem normalize_represents {K ι : Type*} [Field K]
    (v : ι → K) (hv : v ≠ 0) (c : ι) (hc : v c ≠ 0) :
    ∃ hn : (fun j => v j / v c) ≠ 0,
      Projectivization.mk K (fun j => v j / v c) hn = Projectivization.mk K v hv := by
  have hn : (fun j => v j / v c) ≠ 0 := by
    intro h
    have h0 := congrFun h c
    exact one_ne_zero (by simpa only [div_self hc, Pi.zero_apply] using h0)
  refine ⟨hn, (Projectivization.mk_eq_mk_iff' K _ _ _ _).mpr ⟨(v c)⁻¹, ?_⟩⟩
  funext j
  simp only [Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]

/-- Analytic homogeneous lifts are continuous into the actual Zariski topology. -/
theorem continuousAt_of_analytic_lift
    {K E : Type*} [NontriviallyNormedField K]
    [NormedAddCommGroup E] [NormedSpace K E]
    (M : MultiProjectiveSpace K) (e : E → M.Point) (v : E → M.Variable → K) (x : E)
    (hv : ∀ j, AnalyticAt K (fun z => v z j) x)
    (hrep : ∀ z i, ∃ h : (fun j => v z ⟨i, j⟩) ≠ 0,
      Projectivization.mk K (fun j => v z ⟨i, j⟩) h = e z i) :
    @ContinuousAt E M.Point _ M.zariskiTopology e x := by
  apply TopologicalSpace.tendsto_nhds_generateFrom_iff.mpr
  rintro _ ⟨P, D, hP, rfl⟩ hx
  have hpoly : AnalyticAt K (fun z => MvPolynomial.eval (v z) P) x :=
    AnalyticAt.aeval_mvPolynomial hv P
  have hne : MvPolynomial.eval (v x) P ≠ 0 :=
    (M.eval_eq_zero_iff_of_lift (e x) (v x) (hrep x) P D hP).not.mpr hx
  filter_upwards [hpoly.continuousAt.eventually_ne hne] with z hz
  exact (M.eval_eq_zero_iff_of_lift (e z) (v z) (hrep z) P D hP).not.mp hz

/-- A regular map evaluated on analytic projective lifts admits an analytic,
normalized lift near a point with prescribed normalized representative. -/
theorem analytic_normalized_lift
    {K E : Type u} [NontriviallyNormedField K] [CompleteSpace K]
    [NormedAddCommGroup E] [NormedSpace K E]
    {M N : MultiProjectiveSpace K} (e : E → M.Point) (g : E → N.Point)
    (hreg : M.IsRegularAlong N e g)
    (v : E → M.Variable → K) (x : E)
    (hv : ∀ j, AnalyticAt K (fun z => v z j) x)
    (hrep : ∀ z i, ∃ h : (fun j => v z ⟨i, j⟩) ≠ 0,
      Projectivization.mk K (fun j => v z ⟨i, j⟩) h = e z i)
    (c : ∀ i : N.FactorIndex, Fin (N.ambientDimension i + 1))
    (a : N.Variable → K) (ha : ∀ i, a ⟨i, c i⟩ = 1)
    (harep : ∀ i, ∃ h : (fun j => a ⟨i, j⟩) ≠ 0,
      Projectivization.mk K (fun j => a ⟨i, j⟩) h = g x i) :
    ∃ w : E → N.Variable → K, AnalyticAt K w x ∧ w x = a ∧
      (∀ᶠ z in 𝓝 x, (∀ i, w z ⟨i, c i⟩ = 1) ∧
        ∀ i, ∃ h : (fun j => w z ⟨i, j⟩) ≠ 0,
          Projectivization.mk K (fun j => w z ⟨i, j⟩) h = g z i) := by
  classical
  letI : TopologicalSpace M.Point := M.zariskiTopology
  choose U hU hxU D P hP hPlift using hreg x
  let q (z : E) (t : N.Variable) := MvPolynomial.eval (v z) (P t.1 t.2)
  have hq (t : N.Variable) : AnalyticAt K (fun z => q z t) x :=
    AnalyticAt.aeval_mvPolynomial hv (P t.1 t.2)
  have hUevent : ∀ᶠ z in 𝓝 x, ∀ i, e z ∈ U i := by
    rw [Filter.eventually_all]
    intro i
    exact (continuousAt_of_analytic_lift M e v x hv hrep).eventually ((hU i).mem_nhds (hxU i))
  have hqrep : ∀ᶠ z in 𝓝 x, ∀ i, ∃ h : (fun j => q z ⟨i, j⟩) ≠ 0,
      Projectivization.mk K (fun j => q z ⟨i, j⟩) h = g z i := by
    filter_upwards [hUevent] with z hz i
    obtain ⟨hn, he⟩ := hPlift i z (hz i)
    obtain ⟨hn', he'⟩ := M.homogeneous_tuple_lift (e z) (v z) (hrep z)
      (P i) (D i) (hP i) hn
    exact ⟨hn', he'.trans he⟩
  have hpiv (i : N.FactorIndex) : q x ⟨i, c i⟩ ≠ 0 := by
    obtain ⟨hn, he⟩ := hqrep.self_of_nhds i
    obtain ⟨hn', he'⟩ := harep i
    exact pivot_ne_zero (he.trans he'.symm) (c i) (ha i)
  let w (z : E) (t : N.Variable) := q z t / q z ⟨t.1, c t.1⟩
  have hw : AnalyticAt K w x := by
    apply analyticAt_pi_iff.mpr
    intro t
    exact (hq t).div (hq _) (hpiv t.1)
  have hpivevent : ∀ᶠ z in 𝓝 x, ∀ i, q z ⟨i, c i⟩ ≠ 0 := by
    rw [Filter.eventually_all]
    intro i
    exact (hq _).continuousAt.eventually_ne (hpiv i)
  have hwrep : ∀ᶠ z in 𝓝 x, (∀ i, w z ⟨i, c i⟩ = 1) ∧
      ∀ i, ∃ h : (fun j => w z ⟨i, j⟩) ≠ 0,
        Projectivization.mk K (fun j => w z ⟨i, j⟩) h = g z i := by
    filter_upwards [hqrep, hpivevent] with z hz hpz
    refine ⟨fun i => div_self (hpz i), fun i => ?_⟩
    obtain ⟨hn, he⟩ := hz i
    obtain ⟨hn', he'⟩ := normalize_represents (fun j => q z ⟨i, j⟩) hn (c i) (hpz i)
    exact ⟨hn', he'.trans he⟩
  refine ⟨w, hw, ?_, hwrep⟩
  funext t
  obtain ⟨hn, he⟩ := hwrep.self_of_nhds.2 t.1
  obtain ⟨hn', he'⟩ := harep t.1
  exact congrFun (normalized_lifts_eq (he.trans he'.symm) (c t.1)
    (hwrep.self_of_nhds.1 t.1) (ha t.1)) t.2

end PhilipponMultiplicity.AnalyticRegularMaps

end

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open Filter
open scoped Topology

namespace PhilipponMultiplicity.AnalyticRegularMaps
universe u

/-- Analytic normalized parameter lifts turn algebraic addition into an
analytic normalized ambient-coordinate function. -/
theorem addition_analytic_lift
    {K : Type u} [NontriviallyNormedField K] [CompleteSpace K]
    (G : EmbeddedGroupProduct K) (d : ℕ)
    (φ : (Fin d → K) → G.Point) (f : (Fin d → K) → G.ambient.Variable → K)
    (c : ∀ i : G.FactorIndex, Fin ((G.factor i).ambientDimension + 1))
    (hφ : φ 0 = 0) (hf : AnalyticAt K f 0)
    (hc : ∀ u i, f u ⟨i, c i⟩ = 1)
    (hrep : ∀ u i, ∃ h : (fun j => f u ⟨i, j⟩) ≠ 0,
      Projectivization.mk K (fun j => f u ⟨i, j⟩) h = G.embedding (φ u) i) :
    ∃ w : ((Fin d → K) × (Fin d → K)) → G.ambient.Variable → K,
      AnalyticAt K w 0 ∧ w 0 = f 0 ∧
      (∀ᶠ z in 𝓝 (0 : (Fin d → K) × (Fin d → K)),
        (∀ i, w z ⟨i, c i⟩ = 1) ∧
        ∀ i, ∃ h : (fun j => w z ⟨i, j⟩) ≠ 0,
          Projectivization.mk K (fun j => w z ⟨i, j⟩) h =
            G.embedding (φ z.1 + φ z.2) i) := by
  classical
  have hfactor (i : G.FactorIndex) :
      ∃ wi : ((Fin d → K) × (Fin d → K)) →
          (projectiveSpace K (G.factor i).ambientDimension).Variable → K,
        AnalyticAt K wi 0 ∧
        wi 0 = (fun t => f 0 ⟨i, t.2⟩) ∧
        (∀ᶠ z in 𝓝 (0 : (Fin d → K) × (Fin d → K)),
          (∀ b, wi z ⟨b, c i⟩ = 1) ∧
          ∀ b, ∃ h : (fun j => wi z ⟨b, j⟩) ≠ 0,
            Projectivization.mk K (fun j => wi z ⟨b, j⟩) h =
              ((φ z.1 i) + (φ z.2 i)).val) := by
    let M := projectiveSquare K (G.factor i).ambientDimension
    let N := projectiveSpace K (G.factor i).ambientDimension
    let e (z : (Fin d → K) × (Fin d → K)) : M.Point :=
      fun b => if b.val = 0 then (φ z.1 i).val else (φ z.2 i).val
    let g (z : (Fin d → K) × (Fin d → K)) : N.Point :=
      fun _ => ((φ z.1 i) + (φ z.2 i)).val
    let v (z : (Fin d → K) × (Fin d → K)) (t : M.Variable) :=
      if t.1.val = 0 then f z.1 ⟨i, t.2⟩ else f z.2 ⟨i, t.2⟩
    have hreg : M.IsRegularAlong N e g := by
      intro z b
      obtain ⟨U, hU, hz, D, P, hP, hR⟩ := (G.factor i).addition_regular
        (φ z.1 i, φ z.2 i) b
      exact ⟨U, hU, hz, D, P, hP, fun y hy => hR (φ y.1 i, φ y.2 i) hy⟩
    have hv (t : M.Variable) : AnalyticAt K (fun z => v z t) 0 := by
      dsimp only [v]
      split_ifs
      · exact (analyticAt_pi_iff.mp hf ⟨i, t.2⟩).comp
          (f := fun z : (Fin d → K) × (Fin d → K) => z.1)
          (x := (0 : (Fin d → K) × (Fin d → K))) analyticAt_fst
      · exact (analyticAt_pi_iff.mp hf ⟨i, t.2⟩).comp
          (f := fun z : (Fin d → K) × (Fin d → K) => z.2)
          (x := (0 : (Fin d → K) × (Fin d → K))) analyticAt_snd
    have hvr (z : (Fin d → K) × (Fin d → K)) (b : M.FactorIndex) :
        ∃ h : (fun j => v z ⟨b, j⟩) ≠ 0,
          Projectivization.mk K (fun j => v z ⟨b, j⟩) h = e z b := by
      dsimp only [v, e]
      split_ifs
      · exact hrep z.1 i
      · exact hrep z.2 i
    have har (b : N.FactorIndex) :
        ∃ h : (fun j => f 0 ⟨i, j⟩) ≠ 0,
          Projectivization.mk K (fun j => f 0 ⟨i, j⟩) h = g 0 b := by
      simpa [g, hφ, EmbeddedGroupProduct.embedding] using hrep 0 i
    exact analytic_normalized_lift e g hreg v 0 hv hvr (fun _ => c i)
      (fun t => f 0 ⟨i, t.2⟩) (fun _ => hc 0 i) har
  choose wi hwi hwiz hwrep using hfactor
  let w (z : (Fin d → K) × (Fin d → K)) (t : G.ambient.Variable) := wi t.1 z ⟨(0 : Fin 1), t.2⟩
  refine ⟨w, ?_, ?_, ?_⟩
  · apply analyticAt_pi_iff.mpr
    intro t
    exact analyticAt_pi_iff.mp (hwi t.1) ⟨(0 : Fin 1), t.2⟩
  · funext t
    exact congrFun (hwiz t.1) ⟨(0 : Fin 1), t.2⟩
  · have hAll : ∀ᶠ z in 𝓝 (0 : (Fin d → K) × (Fin d → K)),
        ∀ i, (∀ b, wi i z ⟨b, c i⟩ = 1) ∧
          ∀ b, ∃ h : (fun j => wi i z ⟨b, j⟩) ≠ 0,
            Projectivization.mk K (fun j => wi i z ⟨b, j⟩) h =
              ((φ z.1 i) + (φ z.2 i)).val := Filter.eventually_all.mpr hwrep
    filter_upwards [hAll] with z hz
    exact ⟨fun i => (hz i).1 (0 : Fin 1), fun i => (hz i).2 (0 : Fin 1)⟩

end PhilipponMultiplicity.AnalyticRegularMaps

end

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open Filter
open scoped Topology

namespace PhilipponMultiplicity.AnalyticRegularMaps

/-- Transfer the group law through a normalized analytic chart whose inverse
is a continuous linear projection of the centered ambient coordinates. -/
theorem local_addition_of_normalized_chart
    {K : Type*} [NontriviallyNormedField K] [CompleteSpace K]
    (G : EmbeddedGroupProduct K) (d : ℕ)
    (φ : (Fin d → K) → G.Point) (f : (Fin d → K) → G.ambient.Variable → K)
    (c : ∀ i : G.FactorIndex, Fin ((G.factor i).ambientDimension + 1))
    (ρ : (G.ambient.Variable → K) →L[K] (Fin d → K))
    (hφ : φ 0 = 0) (hf : AnalyticAt K f 0)
    (hc : ∀ u i, f u ⟨i, c i⟩ = 1)
    (hrep : ∀ u i, ∃ h : (fun j => f u ⟨i, j⟩) ≠ 0,
      Projectivization.mk K (fun j => f u ⟨i, j⟩) h = G.embedding (φ u) i)
    (hleft : ∀ᶠ u in 𝓝 (0 : Fin d → K), ρ (f u - f 0) = u)
    (hright : ∀ᶠ v in 𝓝 (f 0), (∀ i, v ⟨i, c i⟩ = 1) →
      ∀ x : G.Point,
        (∀ i, ∃ h : (fun j => v ⟨i, j⟩) ≠ 0,
          Projectivization.mk K (fun j => v ⟨i, j⟩) h = G.embedding x i) →
        φ (ρ (v - f 0)) = x) :
    ∃ μ : ((Fin d → K) × (Fin d → K)) → (Fin d → K),
      AnalyticAt K μ 0 ∧ μ 0 = 0 ∧
      (∀ᶠ u in 𝓝 (0 : Fin d → K), μ (u, 0) = u) ∧
      (∀ᶠ u in 𝓝 (0 : Fin d → K), μ (0, u) = u) ∧
      (∀ᶠ z in 𝓝 (0 : (Fin d → K) × (Fin d → K)),
        φ (μ z) = φ z.1 + φ z.2) := by
  obtain ⟨w, hw, hw0, hwrep⟩ := addition_analytic_lift G d φ f c hφ hf hc hrep
  let μ (z : (Fin d → K) × (Fin d → K)) := ρ (w z - f 0)
  have hμ : AnalyticAt K μ 0 := (ρ.analyticAt _).comp (hw.sub analyticAt_const)
  have hzero : μ 0 = 0 := by simp [μ, hw0]
  have hwl : ∀ᶠ u in 𝓝 (0 : Fin d → K), w (u, 0) = f u := by
    have ht : Tendsto (fun u : Fin d → K => (u, (0 : Fin d → K))) (𝓝 0) (𝓝 0) :=
      (continuous_id.prodMk continuous_const).continuousAt
    filter_upwards [ht.eventually hwrep] with u hu
    funext t
    obtain ⟨hn, he⟩ := hu.2 t.1
    obtain ⟨hn', he'⟩ := hrep u t.1
    have he'' : Projectivization.mk K (fun j => w (u, 0) ⟨t.1, j⟩) hn =
        Projectivization.mk K (fun j => f u ⟨t.1, j⟩) hn' := by
      rw [he, he']
      simp only [hφ, add_zero]
    exact congrFun (normalized_lifts_eq he'' (c t.1) (hu.1 t.1) (hc u t.1)) t.2
  have hwr : ∀ᶠ u in 𝓝 (0 : Fin d → K), w (0, u) = f u := by
    have ht : Tendsto (fun u : Fin d → K => ((0 : Fin d → K), u)) (𝓝 0) (𝓝 0) :=
      (continuous_const.prodMk continuous_id).continuousAt
    filter_upwards [ht.eventually hwrep] with u hu
    funext t
    obtain ⟨hn, he⟩ := hu.2 t.1
    obtain ⟨hn', he'⟩ := hrep u t.1
    have he'' : Projectivization.mk K (fun j => w (0, u) ⟨t.1, j⟩) hn =
        Projectivization.mk K (fun j => f u ⟨t.1, j⟩) hn' := by
      rw [he, he']
      simp only [hφ, zero_add]
    exact congrFun (normalized_lifts_eq he'' (c t.1) (hu.1 t.1) (hc u t.1)) t.2
  refine ⟨μ, hμ, hzero, ?_, ?_, ?_⟩
  · filter_upwards [hwl, hleft] with u hu hu'
    simpa only [μ, hu] using hu'
  · filter_upwards [hwr, hleft] with u hu hu'
    simpa only [μ, hu] using hu'
  · have ht : Tendsto w (𝓝 0) (𝓝 (f 0)) := by
      simpa only [hw0] using hw.continuousAt.tendsto
    filter_upwards [hwrep, ht.eventually hright] with z hz hz'
    exact hz' hz.1 (φ z.1 + φ z.2) hz.2

end PhilipponMultiplicity.AnalyticRegularMaps

namespace PhilipponMultiplicity

private theorem analyticChart_complete {K : Type*} [NontriviallyNormedField K]
    (hK : IsPhilipponBaseField K) : CompleteSpace K := by
  rcases hK with ⟨e, he⟩ | ⟨p, hp, h⟩
  · exact (he.isUniformInducing.completeSpace_congr e.surjective).mpr inferInstance
  · letI : Fact p.Prime := ⟨hp⟩
    obtain ⟨e, he⟩ := h
    exact (he.isUniformInducing.completeSpace_congr e.surjective).mpr inferInstance

theorem analytic_addition_model_of_normalized_chart
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (G : EmbeddedGroupProduct K)
    (hchart : ∃ (d : ℕ) (φ : (Fin d → K) → G.Point)
      (f : (Fin d → K) → G.ambient.Variable → K)
      (c : ∀ i : G.FactorIndex, Fin ((G.factor i).ambientDimension + 1))
      (ρ : (G.ambient.Variable → K) →L[K] (Fin d → K)),
      φ 0 = 0 ∧ AnalyticAt K f 0 ∧
      (∀ u i, f u ⟨i, c i⟩ = 1) ∧
      (∀ u i, ∃ h : (fun j => f u ⟨i, j⟩) ≠ 0,
        Projectivization.mk K (fun j => f u ⟨i, j⟩) h = G.embedding (φ u) i) ∧
      (∀ᶠ u in 𝓝 (0 : Fin d → K), ρ (f u - f 0) = u) ∧
      (∀ᶠ v in 𝓝 (f 0), (∀ i, v ⟨i, c i⟩ = 1) →
        ∀ x : G.Point,
          (∀ i, ∃ h : (fun j => v ⟨i, j⟩) ≠ 0,
            Projectivization.mk K (fun j => v ⟨i, j⟩) h = G.embedding x i) →
          φ (ρ (v - f 0)) = x) ∧
      (∀ U : Set (Fin d → K), U ∈ 𝓝 0 →
        (@interior _ G.zariskiTopology
          (@closure _ G.zariskiTopology (φ '' U))).Nonempty)) :
    ∃ (d : ℕ) (φ : (Fin d → K) → G.Point)
      (μ : ((Fin d → K) × (Fin d → K)) → (Fin d → K)),
      φ 0 = 0 ∧ AnalyticAt K μ 0 ∧ μ 0 = 0 ∧
      (∀ᶠ u in 𝓝 (0 : Fin d → K), μ (u, 0) = u) ∧
      (∀ᶠ u in 𝓝 (0 : Fin d → K), μ (0, u) = u) ∧
      (∀ᶠ z in 𝓝 (0 : (Fin d → K) × (Fin d → K)),
        φ (μ z) = φ z.1 + φ z.2) ∧
      (∀ U : Set (Fin d → K), U ∈ 𝓝 0 →
        (@interior _ G.zariskiTopology
          (@closure _ G.zariskiTopology (φ '' U))).Nonempty) := by
  letI : CompleteSpace K := analyticChart_complete hK
  obtain ⟨d, φ, f, c, ρ, hφ, hf, hc, hrep, hleft, hright, hdense⟩ := hchart
  obtain ⟨μ, hμ, hz, hl, hr, hcompat⟩ := AnalyticRegularMaps.local_addition_of_normalized_chart
    G d φ f c ρ hφ hf hc hrep hleft hright
  exact ⟨d, φ, μ, hφ, hμ, hz, hl, hr, hcompat, hdense⟩

end PhilipponMultiplicity

end

open PhilipponMultiplicity Filter Topology

theorem solution
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (G : EmbeddedGroupProduct K) :
    ∃ (d : ℕ) (φ : (Fin d → K) → G.Point)
      (μ : ((Fin d → K) × (Fin d → K)) → (Fin d → K)),
      φ 0 = 0 ∧ AnalyticAt K μ 0 ∧ μ 0 = 0 ∧
      (∀ᶠ u in 𝓝 (0 : Fin d → K), μ (u, 0) = u) ∧
      (∀ᶠ u in 𝓝 (0 : Fin d → K), μ (0, u) = u) ∧
      (∀ᶠ z in 𝓝 (0 : (Fin d → K) × (Fin d → K)),
        φ (μ z) = φ z.1 + φ z.2) ∧
      (∀ U : Set (Fin d → K), U ∈ 𝓝 0 →
        (@interior _ G.zariskiTopology
          (@closure _ G.zariskiTopology (φ '' U))).Nonempty) := by
  exact analytic_addition_model_of_normalized_chart K hK G
    (exists_normalized_analytic_group_chart K hK G)
