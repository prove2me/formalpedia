-- Prove2me | solution 1 for QuantumEcon.Duopoly.proposition_2
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-18T06:42:00.032981+00:00
-- url     : https://prove2.me/submissions/670c55e4-9f72-4eb7-aa03-34f89596da84

-- Research directed by Alexander Richard Towell (queelius); formalization by OpenAI Codex.
-- Source: Francesco Bova, Avi Goldfarb and Roger G. Melko, Quantum Economic Advantage, NBER 29724 (2022).
-- Platform formulation: mikedeng1. Uses the source numerical instance with gamma = 1.
-- Full off-path equilibrium and universal investment uniqueness are proved directly.
import Mathlib
import Definitions.Def_QuantumEcon_Duopoly_Setting
set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
open QuantumEcon.Duopoly SupplierAudit.Competition
namespace CoupledQuantum
def params : Params := ⟨20,2,1,10,8⟩
def strategy (x y : ℝ) : ℝ × ℝ :=
  if 2*(18+x)  ≤  16+y then (0,(16+y)/2)
  else if 2*(16+y)  ≤  18+x then ((18+x)/2,0)
  else ((20+2*x-y)/3,(14+2*y-x)/3)

lemma best_kkt (A q s : ℝ) (hq : 0 ≤ q)
    (h : ∀ z : ℝ, 0 ≤ z → (A-z-s)*z  ≤  (A-q-s)*q) :
    A-2*q-s ≤ 0 ∧ q*(A-2*q-s)=0 := by
  by_cases hd : 0 ≤ A-s
  · have hh := h ((A-s)/2) (by linarith)
    have he : q=(A-s)/2 := by nlinarith [sq_nonneg (q-(A-s)/2)]
    rw [he]
    constructor <;> ring_nf <;> norm_num
  · have hh := h 0 (by norm_num)
    have he : q=0 := by nlinarith [sq_nonneg q]
    rw [he]
    constructor <;> nlinarith

lemma kkt_nash (A D q s : ℝ) (hq : 0 ≤ q) (hs : 0 ≤ s)
    (h₁ : A-2*q-s ≤ 0) (hc₁ : q*(A-2*q-s)=0)
    (h₂ : D-2*s-q ≤ 0) (hc₂ : s*(D-2*s-q)=0) :
    IsCournotNash 1 A 0 D 0 q s := by
  refine ⟨hq,hs,?_,?_⟩
  · intro z hz
    dsimp [cournotPayoff]
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hz h₁,sq_nonneg (z-q)]
  · intro z hz
    dsimp [cournotPayoff]
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hz h₂,sq_nonneg (z-s)]

lemma stage2_kkt (x y q s : ℝ) (h : IsStage2Nash params x y q s) :
    0 ≤ q ∧ 0 ≤ s ∧ 18+x-2*q-s ≤ 0 ∧ q*(18+x-2*q-s)=0 ∧
      16+y-2*s-q ≤ 0 ∧ s*(16+y-2*s-q)=0 := by
  have h₁ := best_kkt (18+x) q s h.1 (by
    intro z hz
    have hh := h.2.2.1 z hz
    dsimp [cournotPayoff,params] at hh
    nlinarith)
  have h₂ := best_kkt (16+y) s q h.2.1 (by
    intro z hz
    have hh := h.2.2.2 z hz
    dsimp [cournotPayoff,params] at hh
    nlinarith)
  exact ⟨h.1,h.2.1,h₁.1,h₁.2,h₂.1,h₂.2⟩

lemma stage2_exists (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    IsStage2Nash params x y (strategy x y).1 (strategy x y).2 := by
  have h : IsCournotNash 1 (18+x) 0 (16+y) 0 (strategy x y).1 (strategy x y).2 := by
    unfold strategy
    split_ifs with h₁ h₂
    · apply kkt_nash <;> dsimp <;> nlinarith
    · apply kkt_nash <;> dsimp <;> nlinarith
    · apply kkt_nash <;> dsimp <;> nlinarith
  refine ⟨h.1,h.2.1,?_,?_⟩
  · intro z hz
    have hh := h.2.2.1 z hz
    dsimp [cournotPayoff,params]
    dsimp [cournotPayoff] at hh
    nlinarith
  · intro z hz
    have hh := h.2.2.2 z hz
    dsimp [cournotPayoff,params]
    dsimp [cournotPayoff] at hh
    nlinarith

lemma stage2_bounds (x y q s : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (h : IsStage2Nash params x y q s) :
    q ≤ (18+x)/2 ∧ s ≤ (16+y)/2 ∧
    profit₁ params x q s=q^2-5*x^2 ∧ profit₂ params y q s=s^2-4*y^2 := by
  obtain ⟨hq,hs,hr,hc,hr',hc'⟩ := stage2_kkt x y q s h
  refine ⟨?_,?_,?_,?_⟩
  · rcases mul_eq_zero.mp hc with hq0|hr0 <;> linarith
  · rcases mul_eq_zero.mp hc' with hs0|hr0 <;> linarith
  · dsimp [profit₁,params]; nlinarith
  · dsimp [profit₂,params]; nlinarith

lemma stage2_interior (x y q s : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hx6 : x ≤ 6) (hy6 : y ≤ 6)
    (h : IsStage2Nash params x y q s) : q=(20+2*x-y)/3 ∧ s=(14+2*y-x)/3 := by
  obtain ⟨hq,hs,hr,hc,hr',hc'⟩ := stage2_kkt x y q s h
  have hb := stage2_bounds x y q s hx hy h
  have hq0 : q≠0 := by intro he; rw [he] at hr; linarith [hb.2.1]
  have hs0 : s≠0 := by intro he; rw [he] at hr'; linarith [hb.1]
  have he₁ := (mul_eq_zero.mp hc).resolve_left hq0
  have he₂ := (mul_eq_zero.mp hc').resolve_left hs0
  constructor <;> linarith

lemma profit₁_large (x y q s : ℝ) (hx : 6 ≤ x) (hy : 0 ≤ y)
    (h : IsStage2Nash params x y q s) : profit₁ params x q s < 0 := by
  have hb := stage2_bounds x y q s (by linarith) hy h
  rw [hb.2.2.1]
  have hq := h.1
  have hqsq : q^2 ≤ ((18+x)/2)^2 := sq_le_sq₀ hq (by linarith) |>.mpr hb.1
  have hxsq : 6*x ≤ x^2 := by nlinarith [sq_nonneg (x-6)]
  nlinarith
lemma profit₂_large (x y q s : ℝ) (hx : 0 ≤ x) (hy : 6 ≤ y)
    (h : IsStage2Nash params x y q s) : profit₂ params y q s < 0 := by
  have hb := stage2_bounds x y q s hx (by linarith) h
  rw [hb.2.2.2]
  have hs := h.2.1
  have hssq : s^2 ≤ ((16+y)/2)^2 := sq_le_sq₀ hs (by linarith) |>.mpr hb.2.1
  have hysq : 6*y ≤ y^2 := by nlinarith [sq_nonneg (y-6)]
  nlinarith

lemma spe_bounded (x y : ℝ) (σ : ℝ → ℝ → ℝ × ℝ) (h : IsSPE params x y σ) : x ≤ 6 ∧ y ≤ 6 := by
  have hx := h.2.1
  have hy := h.2.2.1
  have hcur := h.1 x y hx hy
  have hd1 := stage2_bounds 0 y (σ 0 y).1 (σ 0 y).2 (by norm_num) hy (h.1 0 y (by norm_num) hy)
  have hd2 := stage2_bounds x 0 (σ x 0).1 (σ x 0).2 hx (by norm_num) (h.1 x 0 hx (by norm_num))
  have hp1 := h.2.2.2.1 0 (by norm_num)
  have hp2 := h.2.2.2.2 0 (by norm_num)
  rw [hd1.2.2.1] at hp1
  rw [hd2.2.2.2] at hp2
  constructor
  · by_contra hn
    have hh := profit₁_large x y (σ x y).1 (σ x y).2 (by linarith) hy hcur
    nlinarith [sq_nonneg (σ 0 y).1]
  · by_contra hn
    have hh := profit₂_large x y (σ x y).1 (σ x y).2 hx (by linarith) hcur
    nlinarith [sq_nonneg (σ x 0).2]

lemma spe_unique (x y : ℝ) (σ : ℝ → ℝ → ℝ × ℝ) (h : IsSPE params x y σ) :
    x=102/109 ∧ y=89/109 := by
  have hx := h.2.1
  have hy := h.2.2.1
  have hb := spe_bounded x y σ h
  have hc := stage2_interior x y (σ x y).1 (σ x y).2 hx hy hb.1 hb.2 (h.1 x y hx hy)
  let u := (40-2*y)/41
  let v := (14-x)/16
  have hu : 0 ≤ u ∧ u ≤ 6 := by dsimp [u]; constructor <;> linarith [hb.2]
  have hv : 0 ≤ v ∧ v ≤ 6 := by dsimp [v]; constructor <;> linarith [hb.1]
  have hd1 := stage2_interior u y (σ u y).1 (σ u y).2 hu.1 hy hu.2 hb.2 (h.1 u y hu.1 hy)
  have hd2 := stage2_interior x v (σ x v).1 (σ x v).2 hx hv.1 hb.1 hv.2 (h.1 x v hx hv.1)
  have hp1 := h.2.2.2.1 u hu.1
  have hp2 := h.2.2.2.2 v hv.1
  rw [hc.1,hc.2,hd1.1,hd1.2] at hp1
  rw [hc.1,hc.2,hd2.1,hd2.2] at hp2
  dsimp [profit₁,profit₂,params,u,v] at hp1 hp2
  have he1 : 41*x+2*y=40 := by nlinarith [sq_nonneg (41*x+2*y-40)]
  have he2 : x+16*y=14 := by nlinarith [sq_nonneg (x+16*y-14)]
  constructor <;> linarith

lemma spe_exists : IsSPE params (102/109) (89/109) strategy := by
  have hc := stage2_interior (102/109) (89/109) (strategy (102/109) (89/109)).1
    (strategy (102/109) (89/109)).2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (stage2_exists (102/109) (89/109) (by norm_num) (by norm_num))
  refine ⟨stage2_exists,by norm_num,by norm_num,?_,?_⟩
  · intro z hz
    by_cases hz6 : z ≤ 6
    · have hd := stage2_interior z (89/109) (strategy z (89/109)).1 (strategy z (89/109)).2
        hz (by norm_num) hz6 (by norm_num) (stage2_exists z (89/109) hz (by norm_num))
      rw [hc.1,hc.2,hd.1,hd.2]
      dsimp [profit₁,params]
      nlinarith [sq_nonneg (z-102/109)]
    · have hd := profit₁_large z (89/109) (strategy z (89/109)).1 (strategy z (89/109)).2
        (by linarith) (by norm_num) (stage2_exists z (89/109) hz (by norm_num))
      apply le_trans hd.le
      rw [hc.1,hc.2]
      norm_num [profit₁,params]
  · intro z hz
    by_cases hz6 : z ≤ 6
    · have hd := stage2_interior (102/109) z (strategy (102/109) z).1 (strategy (102/109) z).2
        (by norm_num) hz (by norm_num) hz6 (stage2_exists (102/109) z (by norm_num) hz)
      rw [hc.1,hc.2,hd.1,hd.2]
      dsimp [profit₂,params]
      nlinarith [sq_nonneg (z-89/109)]
    · have hd := profit₂_large (102/109) z (strategy (102/109) z).1 (strategy (102/109) z).2
        (by norm_num) (by linarith) (stage2_exists (102/109) z (by norm_num) hz)
      apply le_trans hd.le
      rw [hc.1,hc.2]
      norm_num [profit₂,params]
end CoupledQuantum
theorem solution :
    ∃ P : Params, Standing P ∧ Lemma1Cond P ∧ P.B₂ < P.B₁ ∧
      (∃ x₁ x₂ : ℝ, ∃ σ : ℝ → ℝ → ℝ × ℝ, IsSPE P x₁ x₂ σ) ∧
      ∀ x₁ x₂ : ℝ, ∀ σ : ℝ → ℝ → ℝ × ℝ,
        IsSPE P x₁ x₂ σ → x₂ < x₁ := by
  refine ⟨CoupledQuantum.params,?_,?_,?_,?_,?_⟩
  · norm_num [Standing,CoupledQuantum.params]
  · norm_num [Lemma1Cond,aStar,Bh₁,Bh₂,Bhh,CoupledQuantum.params]
  · norm_num [CoupledQuantum.params]
  · exact ⟨102/109,89/109,CoupledQuantum.strategy,CoupledQuantum.spe_exists⟩
  · intro x y σ h
    obtain ⟨rfl,rfl⟩ := CoupledQuantum.spe_unique x y σ h
    norm_num
#print axioms solution
