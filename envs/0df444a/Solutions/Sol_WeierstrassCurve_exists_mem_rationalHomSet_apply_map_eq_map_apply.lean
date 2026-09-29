-- Prove2me | solution 1 for WeierstrassCurve.exists_mem_rationalHomSet_apply_map_eq_map_apply
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/5c9cf926-6bbb-58fc-92fd-8c04dc9eea80

import Mathlib
import Definitions.Def_WeierstrassCurve_RationalEnd
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_mem_rationalHomSet_apply_map_eq_map_apply

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open Polynomial
open scoped Polynomial.Bivariate
p2m_open "WeierstrassCurve P2MW.S_WeierstrassCurve_exists_mem_rationalHomSet_apply_map_eq_map_apply.WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point"

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine Affine.Equation Affine.baseChange_negY a₃ map_map a₁ map a₄ a₂ a₆ Affine.degree_polynomial Affine.map_polynomial toAffine Affine.Point map_injective Affine.baseChange_addX Affine.monic_polynomial Affine.Point.map Affine.equation_iff_nonsingular Affine.baseChange_addY evalEvalBC IsRationallyRepresented rationalHomSet zero_mem_rationalHomSet"
namespace RatHomExtend
p2m_open "WeierstrassCurve"

inductive Formula (ι : Type*) where
  | atom : ι → Formula ι
  | and : Formula ι → Formula ι → Formula ι
  | or : Formula ι → Formula ι → Formula ι

namespace Formula

variable {ι : Type*}

def sem {R : Type*} [Zero R] (val : ι → R) : Formula ι → Prop
  | atom i => val i = 0
  | and φ ψ => φ.sem val ∧ ψ.sem val
  | or φ ψ => φ.sem val ∨ ψ.sem val

def polys {A : Type*} [Mul A] (P : ι → A) : Formula ι → List A
  | atom i => [P i]
  | and φ ψ => φ.polys P ++ ψ.polys P
  | or φ ψ => (φ.polys P).flatMap fun f => (ψ.polys P).map fun g => f * g

theorem sem_congr {R : Type*} [Zero R] {v v' : ι → R} (h : ∀ i, v i = v' i) (φ : Formula ι) :
    φ.sem v ↔ φ.sem v' := by
  rw [show v = v' from funext h]

theorem sem_map_iff {A L 𝓕 : Type*} [CommRing A] [Field L] [FunLike 𝓕 A L] [RingHomClass 𝓕 A L]
    (e : 𝓕) (P : ι → A) (φ : Formula ι) :
    φ.sem (fun i => e (P i)) ↔ ∀ p ∈ φ.polys P, e p = 0 := by
  induction φ with
  | atom i => simp [sem, polys]
  | and φ ψ ihφ ihψ =>
    simp only [sem, polys, List.mem_append, ihφ, ihψ]
    exact ⟨fun h p hp => hp.elim (h.1 p) (h.2 p),
      fun h => ⟨fun p hp => h p (Or.inl hp), fun p hp => h p (Or.inr hp)⟩⟩
  | or φ ψ ihφ ihψ =>
    simp only [sem, polys, List.mem_flatMap, List.mem_map, ihφ, ihψ]
    constructor
    · rintro (h | h) p ⟨f, hf, g, hg, rfl⟩
      · rw [map_mul, h f hf, zero_mul]
      · rw [map_mul, h g hg, mul_zero]
    · intro h
      by_contra hc
      push Not at hc
      obtain ⟨⟨f, hf, hf0⟩, ⟨g, hg, hg0⟩⟩ := hc
      exact mul_ne_zero hf0 hg0 (by rw [← map_mul]; exact h _ ⟨f, hf, g, hg, rfl⟩)

theorem transfer {K : Type*} [Field K] [IsAlgClosed K] {V : Type*} [Finite V] {L : Type*}
    [Field L] [Algebra K L] (P : ι → MvPolynomial V K) (φ : Formula ι) (z : V → L)
    (hz : φ.sem fun i => MvPolynomial.aeval z (P i)) :
    ∃ z₀ : V → K, φ.sem fun i => MvPolynomial.aeval z₀ (P i) := by
  by_contra hno
  push Not at hno
  let I : Ideal (MvPolynomial V K) := Ideal.span {p | p ∈ φ.polys P}
  have hZ : MvPolynomial.zeroLocus K I = ∅ := by
    refine Set.eq_empty_iff_forall_notMem.2 fun z₀ hz₀ => hno z₀ ?_
    rw [sem_map_iff]
    exact fun p hp => hz₀ p (Ideal.subset_span hp)
  have h1 : (1 : MvPolynomial V K) ∈ I := by
    have hrad : I.radical = ⊤ := by
      rw [← MvPolynomial.vanishingIdeal_zeroLocus_eq_radical (K := K) I, hZ]
      exact eq_top_iff.2 fun p _ => by simp [MvPolynomial.vanishingIdeal]
    have : (1 : MvPolynomial V K) ∈ I.radical := hrad ▸ Submodule.mem_top
    obtain ⟨n, hn⟩ := this
    simpa using hn
  have hle : I ≤ RingHom.ker (MvPolynomial.aeval z) := by
    rw [Ideal.span_le]
    intro p hp
    rw [SetLike.mem_coe, RingHom.mem_ker]
    exact (sem_map_iff (MvPolynomial.aeval z) P φ).1 hz p hp
  have := hle h1
  rw [RingHom.mem_ker, map_one] at this
  exact one_ne_zero this

end Formula

section Eval

variable {F : Type*} [Field F]

noncomputable def ev (R : Type*) [CommRing R] [Algebra F R] (p : F[X][Y]) (x y : R) : R :=
  (p.map (mapRingHom (algebraMap F R))).evalEval x y

theorem ev_eq_evalEvalBC (L : Type*) [Field L] [Algebra F L] (p : F[X][Y]) (x y : L) :
    ev L p x y = WeierstrassCurve.evalEvalBC L p x y := rfl

theorem map_ev {R R' : Type*} [CommRing R] [CommRing R'] [Algebra F R] [Algebra F R']
    {𝓕 : Type*} [FunLike 𝓕 R R'] [AlgHomClass 𝓕 F R R'] (f : 𝓕) (p : F[X][Y]) (x y : R) :
    f (ev R p x y) = ev R' p (f x) (f y) := by
  have hc : (f : R →+* R').comp (algebraMap F R) = algebraMap F R' :=
    RingHom.ext (AlgHomClass.commutes f)
  rw [ev, ev, ← RingHom.coe_coe, ← map_mapRingHom_evalEval (f : R →+* R'), Polynomial.map_map,
    mapRingHom_comp, hc]

theorem equation_iff_ev (R : Type*) [CommRing R] [Algebra F R] (W : WeierstrassCurve F) (x y : R) :
    (W⁄R).toAffine.Equation x y ↔ ev R W.toAffine.polynomial x y = 0 := by
  have h : (W⁄R).toAffine.polynomial = W.toAffine.polynomial.map (mapRingHom (algebraMap F R)) :=
    WeierstrassCurve.Affine.map_polynomial W (algebraMap F R)
  rw [WeierstrassCurve.Affine.Equation, ev, h]

def tanNum (R : Type*) [CommRing R] [Algebra F R] (W : WeierstrassCurve F) (u v : R) : R :=
  3 * u ^ 2 + 2 * (W⁄R).a₂ * u + (W⁄R).a₄ - (W⁄R).a₁ * v

variable {k₀ : Type*} [Field k₀] [Algebra F k₀]

def gp (R : Type*) [CommRing R] [Algebra k₀ R] (B : Finset k₀) (x : R) : R :=
  ∏ b ∈ B, (x - algebraMap k₀ R b)

theorem gp_ne_zero_iff (L : Type*) [Field L] [Algebra k₀ L] (B : Finset k₀) (x : L) :
    gp L B x ≠ 0 ↔ ∀ b ∈ B, x ≠ algebraMap k₀ L b := by
  simp [gp, Finset.prod_ne_zero_iff, sub_ne_zero]

variable {V : Type*} (L : Type*) [Field L] [Algebra F L] [Algebra k₀ L] [IsScalarTower F k₀ L]
  (z : V → L)

theorem aeval_algebraMap (c : F) :
    MvPolynomial.aeval z (algebraMap F (MvPolynomial V k₀) c) = algebraMap F L c :=
  ((MvPolynomial.aeval z).restrictScalars F).commutes c

theorem aeval_ev (p : F[X][Y]) (a b : MvPolynomial V k₀) :
    MvPolynomial.aeval z (ev (MvPolynomial V k₀) p a b) =
      ev L p (MvPolynomial.aeval z a) (MvPolynomial.aeval z b) :=
  map_ev ((MvPolynomial.aeval z).restrictScalars F) p a b

theorem aeval_gp (B : Finset k₀) (a : MvPolynomial V k₀) :
    MvPolynomial.aeval z (gp (MvPolynomial V k₀) B a) = gp L B (MvPolynomial.aeval z a) := by
  simp [gp, map_prod]

theorem aeval_addX (W : WeierstrassCurve F) (a b c : MvPolynomial V k₀) :
    MvPolynomial.aeval z ((W⁄(MvPolynomial V k₀)).toAffine.addX a b c) =
      (W⁄L).toAffine.addX (MvPolynomial.aeval z a) (MvPolynomial.aeval z b)
        (MvPolynomial.aeval z c) :=
  (WeierstrassCurve.Affine.baseChange_addX (W' := W)
    ((MvPolynomial.aeval z).restrictScalars F) a b c).symm

theorem aeval_addY (W : WeierstrassCurve F) (a b c d : MvPolynomial V k₀) :
    MvPolynomial.aeval z ((W⁄(MvPolynomial V k₀)).toAffine.addY a b c d) =
      (W⁄L).toAffine.addY (MvPolynomial.aeval z a) (MvPolynomial.aeval z b)
        (MvPolynomial.aeval z c) (MvPolynomial.aeval z d) :=
  (WeierstrassCurve.Affine.baseChange_addY (W' := W)
    ((MvPolynomial.aeval z).restrictScalars F) a c b d).symm

theorem aeval_negY (W : WeierstrassCurve F) (a b : MvPolynomial V k₀) :
    MvPolynomial.aeval z ((W⁄(MvPolynomial V k₀)).toAffine.negY a b) =
      (W⁄L).toAffine.negY (MvPolynomial.aeval z a) (MvPolynomial.aeval z b) :=
  (WeierstrassCurve.Affine.baseChange_negY (W' := W)
    ((MvPolynomial.aeval z).restrictScalars F) a b).symm

theorem baseChange_a (R : Type*) [CommRing R] [Algebra F R] (W : WeierstrassCurve F) :
    (W⁄R).a₁ = algebraMap F R W.a₁ ∧ (W⁄R).a₂ = algebraMap F R W.a₂ ∧
      (W⁄R).a₃ = algebraMap F R W.a₃ ∧ (W⁄R).a₄ = algebraMap F R W.a₄ ∧
        (W⁄R).a₆ = algebraMap F R W.a₆ :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem aeval_tanNum (W : WeierstrassCurve F) (a b : MvPolynomial V k₀) :
    MvPolynomial.aeval z (tanNum (MvPolynomial V k₀) W a b) =
      tanNum L W (MvPolynomial.aeval z a) (MvPolynomial.aeval z b) := by
  obtain ⟨h1, h2, -, h4, -⟩ := baseChange_a (MvPolynomial V k₀) W
  obtain ⟨h1', h2', -, h4', -⟩ := baseChange_a L W
  simp only [tanNum, h1, h2, h4, h1', h2', h4', map_sub, map_add, map_mul, map_pow,
    aeval_algebraMap, map_ofNat]

end Eval

section Rho

variable {F : Type*} [Field F] (L : Type*) [Field L] [Algebra F L] [DecidableEq L]
  (W₁ W₂ : WeierstrassCurve F) (nX dX nY dY : F[X][Y])

open scoped Classical in

noncomputable def rho : (W₁⁄L).Point → (W₂⁄L).Point
  | .zero => 0
  | .some x y _ =>
    if h : (W₂⁄L).toAffine.Nonsingular (ev L nX x y / ev L dX x y) (ev L nY x y / ev L dY x y) then
      .some _ _ h
    else 0

theorem rho_zero : rho L W₁ W₂ nX dX nY dY 0 = 0 := rfl

theorem rho_some_of {x y : L} (h : (W₁⁄L).toAffine.Nonsingular x y)
    (h' : (W₂⁄L).toAffine.Nonsingular (ev L nX x y / ev L dX x y) (ev L nY x y / ev L dY x y)) :
    rho L W₁ W₂ nX dX nY dY (.some x y h) = .some _ _ h' := by
  simp only [rho]
  rw [dif_pos h']

omit [DecidableEq L] in
theorem some_eq_some {W : Affine L} {x y x' y' : L} {h : W.Nonsingular x y}
    {h' : W.Nonsingular x' y'} (hx : x = x') (hy : y = y') :
    Point.some x y h = Point.some x' y' h' := by
  subst hx hy; rfl

omit [DecidableEq L] in
theorem isElliptic_baseChange (W : WeierstrassCurve F) [W.IsElliptic] : (W⁄L).IsElliptic :=
  inferInstanceAs ((W.map (algebraMap F L)).IsElliptic)

omit [DecidableEq L] in
theorem nonsingular_of_equation (W : WeierstrassCurve F) [W.IsElliptic] {x y : L}
    (h : (W⁄L).toAffine.Equation x y) : (W⁄L).toAffine.Nonsingular x y :=
  haveI := isElliptic_baseChange L W
  (WeierstrassCurve.Affine.equation_iff_nonsingular).1 h

end Rho

section Systems

variable {F : Type*} [Field F] {k₀ : Type*} [Field k₀] [Algebra F k₀]
variable (W₁ W₂ : WeierstrassCurve F) (nX dX nY dY : F[X][Y]) (B : Finset k₀)

section Semantic

variable (L : Type*) [Field L] [Algebra F L] [Algebra k₀ L] [IsScalarTower F k₀ L] [DecidableEq L]

def GoodX (x : L) : Prop := ∀ b ∈ B, x ≠ algebraMap k₀ L b

def S1 : Prop :=
  ∀ x y : L, (W₁⁄L).toAffine.Equation x y → GoodX B L x → ev L dX x y ≠ 0 ∧ ev L dY x y ≠ 0

def S2 : Prop :=
  ∀ x y : L, (W₁⁄L).toAffine.Equation x y → GoodX B L x → ev L dX x y ≠ 0 → ev L dY x y ≠ 0 →
    (W₂⁄L).toAffine.Equation (ev L nX x y / ev L dX x y) (ev L nY x y / ev L dY x y)

def GEN : Prop :=
  ∀ (x₁ y₁ x₂ y₂ : L) (h₁ : (W₁⁄L).toAffine.Nonsingular x₁ y₁)
    (h₂ : (W₁⁄L).toAffine.Nonsingular x₂ y₂), GoodX B L x₁ → GoodX B L x₂ → x₁ ≠ x₂ →
    GoodX B L ((W₁⁄L).toAffine.addX x₁ x₂ ((W₁⁄L).toAffine.slope x₁ x₂ y₁ y₂)) →
      rho L W₁ W₂ nX dX nY dY (.some _ _ h₁ + .some _ _ h₂) =
        rho L W₁ W₂ nX dX nY dY (.some _ _ h₁) + rho L W₁ W₂ nX dX nY dY (.some _ _ h₂)

variable {W₁ W₂ nX dX nY dY B L}

theorem gp_ne_zero_of_goodX {x : L} (hx : GoodX B L x) : gp L B x ≠ 0 :=
  (gp_ne_zero_iff L B x).2 hx

theorem goodX_of_gp_ne_zero {x : L} (hx : gp L B x ≠ 0) : GoodX B L x :=
  (gp_ne_zero_iff L B x).1 hx

variable [W₂.IsElliptic]

theorem nonsingular_rho (hS1 : S1 W₁ dX dY B L) (hS2 : S2 W₁ W₂ nX dX nY dY B L) {x y : L}
    (h : (W₁⁄L).toAffine.Nonsingular x y) (hx : GoodX B L x) :
    (W₂⁄L).toAffine.Nonsingular (ev L nX x y / ev L dX x y) (ev L nY x y / ev L dY x y) :=
  nonsingular_of_equation L W₂
    (hS2 x y h.left hx (hS1 x y h.left hx).1 (hS1 x y h.left hx).2)

theorem rho_some (hS1 : S1 W₁ dX dY B L) (hS2 : S2 W₁ W₂ nX dX nY dY B L) {x y : L}
    (h : (W₁⁄L).toAffine.Nonsingular x y) (hx : GoodX B L x) :
    rho L W₁ W₂ nX dX nY dY (.some x y h) = .some _ _ (nonsingular_rho hS1 hS2 h hx) :=
  rho_some_of L W₁ W₂ nX dX nY dY h _

end Semantic

inductive I1 | eqn | good | den

inductive V1 | x | y | w
  deriving DecidableEq, Fintype

section Sys1

variable (R : Type*) [CommRing R] [Algebra F R] [Algebra k₀ R]

noncomputable def atoms1 (z : V1 → R) : I1 → R
  | .eqn => ev R W₁.toAffine.polynomial (z .x) (z .y)
  | .good => z .w * gp R B (z .x) - 1
  | .den => ev R dX (z .x) (z .y) * ev R dY (z .x) (z .y)

def Φ1 : Formula I1 := .and (.atom .eqn) (.and (.atom .good) (.atom .den))

variable {R}
variable (L : Type*) [Field L] [Algebra F L] [Algebra k₀ L] [IsScalarTower F k₀ L] [DecidableEq L]

theorem atoms1_aeval (z : V1 → L) (i : I1) :
    MvPolynomial.aeval z (atoms1 W₁ dX dY B (MvPolynomial V1 k₀) MvPolynomial.X i) =
      atoms1 W₁ dX dY B L z i := by
  cases i <;> simp [atoms1, aeval_ev, aeval_gp, map_sub, map_mul]

variable {W₁ dX dY B L}

theorem exists_sem1_of_not_S1 (h : ¬ S1 W₁ dX dY B L) :
    ∃ z : V1 → L, Φ1.sem (atoms1 W₁ dX dY B L z) := by
  simp only [S1, not_forall, not_and_or, not_not, exists_prop] at h
  obtain ⟨x, y, hxy, hg, hd⟩ := h
  refine ⟨fun v => match v with | .x => x | .y => y | .w => (gp L B x)⁻¹, ?_, ?_, ?_⟩
  · exact (equation_iff_ev L W₁ x y).1 hxy
  · change (gp L B x)⁻¹ * gp L B x - 1 = 0
    rw [inv_mul_cancel₀ (gp_ne_zero_of_goodX hg), sub_self]
  · change ev L dX x y * ev L dY x y = 0
    rcases hd with hd | hd <;> simp [hd]

theorem not_S1_of_sem1 [W₁.IsElliptic] (z : V1 → L) (hz : Φ1.sem (atoms1 W₁ dX dY B L z)) :
    ¬ S1 W₁ dX dY B L := by
  intro hS
  obtain ⟨h1, h2, h3⟩ := hz
  change ev L W₁.toAffine.polynomial (z .x) (z .y) = 0 at h1
  change z .w * gp L B (z .x) - 1 = 0 at h2
  change ev L dX (z .x) (z .y) * ev L dY (z .x) (z .y) = 0 at h3
  have hxy := (equation_iff_ev L W₁ (z .x) (z .y)).2 h1
  have hg : GoodX B L (z .x) :=
    goodX_of_gp_ne_zero (right_ne_zero_of_mul_eq_one (sub_eq_zero.1 h2))
  obtain ⟨hdX, hdY⟩ := hS _ _ hxy hg
  exact mul_ne_zero hdX hdY h3

end Sys1

inductive I2 | eqn | side | ux | vy | fail

inductive V2 | x | y | u | v | w | t
  deriving DecidableEq, Fintype

section Sys2

variable (R : Type*) [CommRing R] [Algebra F R] [Algebra k₀ R]

noncomputable def atoms2 (z : V2 → R) : I2 → R
  | .eqn => ev R W₁.toAffine.polynomial (z .x) (z .y)
  | .side => z .w * (gp R B (z .x) * ev R dX (z .x) (z .y) * ev R dY (z .x) (z .y)) - 1
  | .ux => z .u * ev R dX (z .x) (z .y) - ev R nX (z .x) (z .y)
  | .vy => z .v * ev R dY (z .x) (z .y) - ev R nY (z .x) (z .y)
  | .fail => z .t * ev R W₂.toAffine.polynomial (z .u) (z .v) - 1

def Φ2 : Formula I2 :=
  .and (.atom .eqn) (.and (.atom .side) (.and (.atom .ux) (.and (.atom .vy) (.atom .fail))))

variable {R}
variable (L : Type*) [Field L] [Algebra F L] [Algebra k₀ L] [IsScalarTower F k₀ L] [DecidableEq L]

theorem atoms2_aeval (z : V2 → L) (i : I2) :
    MvPolynomial.aeval z (atoms2 W₁ W₂ nX dX nY dY B (MvPolynomial V2 k₀) MvPolynomial.X i) =
      atoms2 W₁ W₂ nX dX nY dY B L z i := by
  cases i <;> simp [atoms2, aeval_ev, aeval_gp, map_sub, map_mul]

variable {W₁ W₂ nX dX nY dY B L}

theorem exists_sem2_of_not_S2 (h : ¬ S2 W₁ W₂ nX dX nY dY B L) :
    ∃ z : V2 → L, Φ2.sem (atoms2 W₁ W₂ nX dX nY dY B L z) := by
  simp only [S2, not_forall, exists_prop] at h
  obtain ⟨x, y, hxy, hg, hdX, hdY, hfail⟩ := h
  set u := ev L nX x y / ev L dX x y with hu
  set v := ev L nY x y / ev L dY x y with hv
  have hfail' : ev L W₂.toAffine.polynomial u v ≠ 0 := fun h0 =>
    hfail ((equation_iff_ev L W₂ u v).2 h0)
  refine ⟨fun i => match i with
    | .x => x | .y => y | .u => u | .v => v
    | .w => (gp L B x * ev L dX x y * ev L dY x y)⁻¹
    | .t => (ev L W₂.toAffine.polynomial u v)⁻¹, ?_, ?_, ?_, ?_, ?_⟩
  · exact (equation_iff_ev L W₁ x y).1 hxy
  · change (gp L B x * ev L dX x y * ev L dY x y)⁻¹ * (gp L B x * ev L dX x y * ev L dY x y) - 1 = 0
    rw [inv_mul_cancel₀ (mul_ne_zero (mul_ne_zero (gp_ne_zero_of_goodX hg) hdX) hdY), sub_self]
  · change u * ev L dX x y - ev L nX x y = 0
    rw [hu, div_mul_cancel₀ _ hdX, sub_self]
  · change v * ev L dY x y - ev L nY x y = 0
    rw [hv, div_mul_cancel₀ _ hdY, sub_self]
  · change (ev L W₂.toAffine.polynomial u v)⁻¹ * ev L W₂.toAffine.polynomial u v - 1 = 0
    rw [inv_mul_cancel₀ hfail', sub_self]

theorem not_S2_of_sem2 (z : V2 → L) (hz : Φ2.sem (atoms2 W₁ W₂ nX dX nY dY B L z)) :
    ¬ S2 W₁ W₂ nX dX nY dY B L := by
  intro hS
  obtain ⟨h1, h2, h3, h4, h5⟩ := hz
  change ev L W₁.toAffine.polynomial (z .x) (z .y) = 0 at h1
  change z .w * (gp L B (z .x) * ev L dX (z .x) (z .y) * ev L dY (z .x) (z .y)) - 1 = 0 at h2
  change z .u * ev L dX (z .x) (z .y) - ev L nX (z .x) (z .y) = 0 at h3
  change z .v * ev L dY (z .x) (z .y) - ev L nY (z .x) (z .y) = 0 at h4
  change z .t * ev L W₂.toAffine.polynomial (z .u) (z .v) - 1 = 0 at h5
  have hxy := (equation_iff_ev L W₁ (z .x) (z .y)).2 h1
  have hside := right_ne_zero_of_mul_eq_one (sub_eq_zero.1 h2)
  have hdY : ev L dY (z .x) (z .y) ≠ 0 := right_ne_zero_of_mul hside
  have hdX : ev L dX (z .x) (z .y) ≠ 0 := right_ne_zero_of_mul (left_ne_zero_of_mul hside)
  have hg : GoodX B L (z .x) :=
    goodX_of_gp_ne_zero (left_ne_zero_of_mul (left_ne_zero_of_mul hside))
  have hu : z .u = ev L nX (z .x) (z .y) / ev L dX (z .x) (z .y) := by
    rw [eq_div_iff hdX]; exact sub_eq_zero.1 h3
  have hv : z .v = ev L nY (z .x) (z .y) / ev L dY (z .x) (z .y) := by
    rw [eq_div_iff hdY]; exact sub_eq_zero.1 h4
  have hfail := right_ne_zero_of_mul_eq_one (sub_eq_zero.1 h5)
  rw [hu, hv] at hfail
  exact hfail ((equation_iff_ev L W₂ _ _).1 (hS _ _ hxy hg hdX hdY))

end Sys2

inductive I3
  | e1 | e2 | e3 | e4 | e5 | e6 | e7 | e8 | e9 | e10
  | c1 | c2 | s1 | s2 | s3 | s4 | r1 | r2

inductive V3
  | x₁ | y₁ | x₂ | y₂ | l | u₁ | v₁ | u₂ | v₂ | u₃ | v₃ | l' | w | w₂ | t₁ | t₂
  deriving DecidableEq, Fintype

section Sys3

variable (R : Type*) [CommRing R] [Algebra F R] [Algebra k₀ R]

def X3 (z : V3 → R) : R := (W₁⁄R).toAffine.addX (z .x₁) (z .x₂) (z .l)

def Y3 (z : V3 → R) : R := (W₁⁄R).toAffine.addY (z .x₁) (z .x₂) (z .y₁) (z .l)

noncomputable def side3 (z : V3 → R) : R :=
  (z .x₁ - z .x₂) * gp R B (z .x₁) * gp R B (z .x₂) * gp R B (X3 W₁ R z) *
    ev R dX (z .x₁) (z .y₁) * ev R dY (z .x₁) (z .y₁) *
    ev R dX (z .x₂) (z .y₂) * ev R dY (z .x₂) (z .y₂) *
    ev R dX (X3 W₁ R z) (Y3 W₁ R z) * ev R dY (X3 W₁ R z) (Y3 W₁ R z)

noncomputable def atoms3 (z : V3 → R) : I3 → R
  | .e1 => ev R W₁.toAffine.polynomial (z .x₁) (z .y₁)
  | .e2 => ev R W₁.toAffine.polynomial (z .x₂) (z .y₂)
  | .e3 => z .l * (z .x₁ - z .x₂) - (z .y₁ - z .y₂)
  | .e4 => z .w * side3 W₁ dX dY B R z - 1
  | .e5 => z .u₁ * ev R dX (z .x₁) (z .y₁) - ev R nX (z .x₁) (z .y₁)
  | .e6 => z .v₁ * ev R dY (z .x₁) (z .y₁) - ev R nY (z .x₁) (z .y₁)
  | .e7 => z .u₂ * ev R dX (z .x₂) (z .y₂) - ev R nX (z .x₂) (z .y₂)
  | .e8 => z .v₂ * ev R dY (z .x₂) (z .y₂) - ev R nY (z .x₂) (z .y₂)
  | .e9 => z .u₃ * ev R dX (X3 W₁ R z) (Y3 W₁ R z) - ev R nX (X3 W₁ R z) (Y3 W₁ R z)
  | .e10 => z .v₃ * ev R dY (X3 W₁ R z) (Y3 W₁ R z) - ev R nY (X3 W₁ R z) (Y3 W₁ R z)
  | .c1 => z .u₁ - z .u₂
  | .c2 => z .v₁ - (W₂⁄R).toAffine.negY (z .u₂) (z .v₂)
  | .s1 => z .w₂ * (z .u₁ - z .u₂) - 1
  | .s2 => z .l' * (z .u₁ - z .u₂) - (z .v₁ - z .v₂)
  | .s3 => z .w₂ * (z .v₁ - (W₂⁄R).toAffine.negY (z .u₂) (z .v₂)) - 1
  | .s4 => z .l' * (z .v₁ - (W₂⁄R).toAffine.negY (z .u₁) (z .v₁)) - tanNum R W₂ (z .u₁) (z .v₁)
  | .r1 => z .t₁ * (z .u₃ - (W₂⁄R).toAffine.addX (z .u₁) (z .u₂) (z .l')) - 1
  | .r2 => z .t₂ * (z .v₃ - (W₂⁄R).toAffine.addY (z .u₁) (z .u₂) (z .v₁) (z .l')) - 1

def Φ3common : Formula I3 :=
  .and (.atom .e1) (.and (.atom .e2) (.and (.atom .e3) (.and (.atom .e4) (.and (.atom .e5)
    (.and (.atom .e6) (.and (.atom .e7) (.and (.atom .e8) (.and (.atom .e9) (.atom .e10)))))))))

def Φ3fail : Formula I3 :=
  .or (.and (.atom .c1) (.atom .c2))
    (.and (.or (.and (.atom .s1) (.atom .s2)) (.and (.atom .c1) (.and (.atom .s3) (.atom .s4))))
      (.or (.atom .r1) (.atom .r2)))

def Φ3 : Formula I3 := .and Φ3common Φ3fail

variable {R}
variable (L : Type*) [Field L] [Algebra F L] [Algebra k₀ L] [IsScalarTower F k₀ L] [DecidableEq L]

theorem aeval_X3 (z : V3 → L) :
    MvPolynomial.aeval z (X3 W₁ (MvPolynomial V3 k₀) MvPolynomial.X) = X3 W₁ L z := by
  unfold X3
  rw [aeval_addX]
  simp only [MvPolynomial.aeval_X]

theorem aeval_Y3 (z : V3 → L) :
    MvPolynomial.aeval z (Y3 W₁ (MvPolynomial V3 k₀) MvPolynomial.X) = Y3 W₁ L z := by
  unfold Y3
  rw [aeval_addY]
  simp only [MvPolynomial.aeval_X]

theorem aeval_side3 (z : V3 → L) :
    MvPolynomial.aeval z (side3 W₁ dX dY B (MvPolynomial V3 k₀) MvPolynomial.X) =
      side3 W₁ dX dY B L z := by
  simp only [side3, map_mul, map_sub, aeval_gp, aeval_ev, aeval_X3, aeval_Y3, MvPolynomial.aeval_X]

theorem atoms3_aeval (z : V3 → L) (i : I3) :
    MvPolynomial.aeval z (atoms3 W₁ W₂ nX dX nY dY B (MvPolynomial V3 k₀) MvPolynomial.X i) =
      atoms3 W₁ W₂ nX dX nY dY B L z i := by
  cases i <;> simp only [atoms3, aeval_ev, map_sub, map_mul, map_one, aeval_side3,
    aeval_X3, aeval_Y3, aeval_addX, aeval_addY, aeval_negY, aeval_tanNum, MvPolynomial.aeval_X]

variable {W₁ W₂ nX dX nY dY B L}
variable [W₁.IsElliptic] [W₂.IsElliptic]

theorem slope_tangent_aux {u₁ v₁ u₂ v₂ : L} (he₁ : (W₂⁄L).toAffine.Equation u₁ v₁)
    (he₂ : (W₂⁄L).toAffine.Equation u₂ v₂) (hu : u₁ = u₂)
    (hv : v₁ ≠ (W₂⁄L).toAffine.negY u₂ v₂) :
    v₁ - (W₂⁄L).toAffine.negY u₁ v₁ ≠ 0 ∧
      (W₂⁄L).toAffine.slope u₁ u₂ v₁ v₂ = tanNum L W₂ u₁ v₁ / (v₁ - (W₂⁄L).toAffine.negY u₁ v₁) := by
  have hv12 : v₁ = v₂ := by
    rcases Y_eq_of_X_eq he₁ he₂ hu with h | h
    · exact h
    · exact absurd h hv
  refine ⟨?_, ?_⟩
  · rw [hu, hv12]; rw [hv12] at hv; exact sub_ne_zero.2 hv
  · rw [slope_of_Y_ne hu hv]
    rfl

theorem not_GEN_of_sem3 (hS1 : S1 W₁ dX dY B L) (hS2 : S2 W₁ W₂ nX dX nY dY B L) (z : V3 → L)
    (hz : Φ3.sem (atoms3 W₁ W₂ nX dX nY dY B L z)) : ¬ GEN W₁ W₂ nX dX nY dY B L := by
  intro hG
  obtain ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩, hfail⟩ := hz
  change ev L W₁.toAffine.polynomial (z .x₁) (z .y₁) = 0 at h1
  change ev L W₁.toAffine.polynomial (z .x₂) (z .y₂) = 0 at h2
  change z .l * (z .x₁ - z .x₂) - (z .y₁ - z .y₂) = 0 at h3
  change z .w * side3 W₁ dX dY B L z - 1 = 0 at h4
  change z .u₁ * ev L dX (z .x₁) (z .y₁) - ev L nX (z .x₁) (z .y₁) = 0 at h5
  change z .v₁ * ev L dY (z .x₁) (z .y₁) - ev L nY (z .x₁) (z .y₁) = 0 at h6
  change z .u₂ * ev L dX (z .x₂) (z .y₂) - ev L nX (z .x₂) (z .y₂) = 0 at h7
  change z .v₂ * ev L dY (z .x₂) (z .y₂) - ev L nY (z .x₂) (z .y₂) = 0 at h8
  change z .u₃ * ev L dX (X3 W₁ L z) (Y3 W₁ L z) - ev L nX (X3 W₁ L z) (Y3 W₁ L z) = 0 at h9
  change z .v₃ * ev L dY (X3 W₁ L z) (Y3 W₁ L z) - ev L nY (X3 W₁ L z) (Y3 W₁ L z) = 0 at h10
  have he₁ := (equation_iff_ev L W₁ _ _).2 h1
  have he₂ := (equation_iff_ev L W₁ _ _).2 h2
  have hn₁ := nonsingular_of_equation L W₁ he₁
  have hn₂ := nonsingular_of_equation L W₁ he₂
  have hside : side3 W₁ dX dY B L z ≠ 0 := right_ne_zero_of_mul_eq_one (sub_eq_zero.1 h4)
  simp only [side3, mul_ne_zero_iff] at hside
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hx12, hg₁⟩, hg₂⟩, hg₃⟩, hdX₁⟩, hdY₁⟩, hdX₂⟩, hdY₂⟩, hdX₃⟩, hdY₃⟩ := hside
  have hx12' : z .x₁ ≠ z .x₂ := sub_ne_zero.1 hx12
  have hl : z .l = (W₁⁄L).toAffine.slope (z .x₁) (z .x₂) (z .y₁) (z .y₂) := by
    rw [slope_of_X_ne hx12', eq_div_iff hx12]; exact sub_eq_zero.1 h3
  have hX3 : X3 W₁ L z = (W₁⁄L).toAffine.addX (z .x₁) (z .x₂)
      ((W₁⁄L).toAffine.slope (z .x₁) (z .x₂) (z .y₁) (z .y₂)) := by
    simp only [X3, hl]
  have hY3 : Y3 W₁ L z = (W₁⁄L).toAffine.addY (z .x₁) (z .x₂) (z .y₁)
      ((W₁⁄L).toAffine.slope (z .x₁) (z .x₂) (z .y₁) (z .y₂)) := by
    simp only [Y3, hl]
  rw [hX3] at hg₃
  rw [hX3, hY3] at h9 h10 hdX₃ hdY₃
  have hgood₁ : GoodX B L (z .x₁) := goodX_of_gp_ne_zero hg₁
  have hgood₂ : GoodX B L (z .x₂) := goodX_of_gp_ne_zero hg₂
  have hgood₃ := goodX_of_gp_ne_zero hg₃

  have h₃ : (W₁⁄L).toAffine.Nonsingular _ _ := nonsingular_add hn₁ hn₂ fun hxy => hx12' hxy.left
  have hadd := hG _ _ _ _ hn₁ hn₂ hgood₁ hgood₂ hx12' hgood₃
  rw [add_of_X_ne hx12', rho_some hS1 hS2 h₃ hgood₃, rho_some hS1 hS2 hn₁ hgood₁,
    rho_some hS1 hS2 hn₂ hgood₂] at hadd

  have hu₁ : z .u₁ = ev L nX (z .x₁) (z .y₁) / ev L dX (z .x₁) (z .y₁) := by
    rw [eq_div_iff hdX₁]; exact sub_eq_zero.1 h5
  have hv₁ : z .v₁ = ev L nY (z .x₁) (z .y₁) / ev L dY (z .x₁) (z .y₁) := by
    rw [eq_div_iff hdY₁]; exact sub_eq_zero.1 h6
  have hu₂ : z .u₂ = ev L nX (z .x₂) (z .y₂) / ev L dX (z .x₂) (z .y₂) := by
    rw [eq_div_iff hdX₂]; exact sub_eq_zero.1 h7
  have hv₂ : z .v₂ = ev L nY (z .x₂) (z .y₂) / ev L dY (z .x₂) (z .y₂) := by
    rw [eq_div_iff hdY₂]; exact sub_eq_zero.1 h8
  have hu₃ : z .u₃ = ev L nX
      ((W₁⁄L).toAffine.addX (z .x₁) (z .x₂) ((W₁⁄L).toAffine.slope (z .x₁) (z .x₂) (z .y₁) (z .y₂)))
      ((W₁⁄L).toAffine.addY (z .x₁) (z .x₂) (z .y₁)
        ((W₁⁄L).toAffine.slope (z .x₁) (z .x₂) (z .y₁) (z .y₂))) /
      ev L dX
      ((W₁⁄L).toAffine.addX (z .x₁) (z .x₂) ((W₁⁄L).toAffine.slope (z .x₁) (z .x₂) (z .y₁) (z .y₂)))
      ((W₁⁄L).toAffine.addY (z .x₁) (z .x₂) (z .y₁)
        ((W₁⁄L).toAffine.slope (z .x₁) (z .x₂) (z .y₁) (z .y₂))) := by
    rw [eq_div_iff hdX₃]; exact sub_eq_zero.1 h9
  have hv₃ : z .v₃ = ev L nY
      ((W₁⁄L).toAffine.addX (z .x₁) (z .x₂) ((W₁⁄L).toAffine.slope (z .x₁) (z .x₂) (z .y₁) (z .y₂)))
      ((W₁⁄L).toAffine.addY (z .x₁) (z .x₂) (z .y₁)
        ((W₁⁄L).toAffine.slope (z .x₁) (z .x₂) (z .y₁) (z .y₂))) /
      ev L dY
      ((W₁⁄L).toAffine.addX (z .x₁) (z .x₂) ((W₁⁄L).toAffine.slope (z .x₁) (z .x₂) (z .y₁) (z .y₂)))
      ((W₁⁄L).toAffine.addY (z .x₁) (z .x₂) (z .y₁)
        ((W₁⁄L).toAffine.slope (z .x₁) (z .x₂) (z .y₁) (z .y₂))) := by
    rw [eq_div_iff hdY₃]; exact sub_eq_zero.1 h10

  set U₁ := ev L nX (z .x₁) (z .y₁) / ev L dX (z .x₁) (z .y₁) with hU₁
  set V₁ := ev L nY (z .x₁) (z .y₁) / ev L dY (z .x₁) (z .y₁) with hV₁
  set U₂ := ev L nX (z .x₂) (z .y₂) / ev L dX (z .x₂) (z .y₂) with hU₂
  set V₂ := ev L nY (z .x₂) (z .y₂) / ev L dY (z .x₂) (z .y₂) with hV₂
  have hE₁ : (W₂⁄L).toAffine.Equation U₁ V₁ := (nonsingular_rho hS1 hS2 hn₁ hgood₁).left
  have hE₂ : (W₂⁄L).toAffine.Equation U₂ V₂ := (nonsingular_rho hS1 hS2 hn₂ hgood₂).left

  simp only [Formula.sem, Φ3fail, atoms3] at hfail
  rw [hu₁, hv₁, hu₂, hv₂, hu₃, hv₃] at hfail
  rcases hfail with ⟨hc1, hc2⟩ | ⟨hslope, hres⟩
  · rw [add_of_Y_eq (sub_eq_zero.1 hc1) (sub_eq_zero.1 hc2)] at hadd
    exact some_ne_zero _ hadd
  ·
    have hkey : ¬ (U₁ = U₂ ∧ V₁ = (W₂⁄L).toAffine.negY U₂ V₂) ∧
        z .l' = (W₂⁄L).toAffine.slope U₁ U₂ V₁ V₂ := by
      rcases hslope with ⟨hs1, hs2⟩ | ⟨hc1, hs3, hs4⟩
      · have hu12 : U₁ - U₂ ≠ 0 := right_ne_zero_of_mul_eq_one (sub_eq_zero.1 hs1)
        refine ⟨fun h => hu12 (sub_eq_zero.2 h.1), ?_⟩
        rw [slope_of_X_ne (sub_ne_zero.1 hu12), eq_div_iff hu12]
        exact sub_eq_zero.1 hs2
      · have hu12 : U₁ = U₂ := sub_eq_zero.1 hc1
        have hv12 : V₁ ≠ (W₂⁄L).toAffine.negY U₂ V₂ :=
          sub_ne_zero.1 (right_ne_zero_of_mul_eq_one (sub_eq_zero.1 hs3))
        obtain ⟨hden, hsl⟩ := slope_tangent_aux hE₁ hE₂ hu12 hv12
        refine ⟨fun h => hv12 h.2, ?_⟩
        rw [hsl, eq_div_iff hden]
        exact sub_eq_zero.1 hs4
    obtain ⟨hnot, hl'⟩ := hkey
    rw [add_some hnot] at hadd
    have hinj := Point.some.inj hadd
    rw [← hl'] at hinj
    rcases hres with hr | hr
    · exact right_ne_zero_of_mul_eq_one (sub_eq_zero.1 hr) (sub_eq_zero.2 hinj.1)
    · exact right_ne_zero_of_mul_eq_one (sub_eq_zero.1 hr) (sub_eq_zero.2 hinj.2)

theorem exists_sem3_of_not_GEN (hS1 : S1 W₁ dX dY B L) (hS2 : S2 W₁ W₂ nX dX nY dY B L)
    (h : ¬ GEN W₁ W₂ nX dX nY dY B L) :
    ∃ z : V3 → L, Φ3.sem (atoms3 W₁ W₂ nX dX nY dY B L z) := by
  simp only [GEN, not_forall, exists_prop] at h
  obtain ⟨x₁, y₁, x₂, y₂, hn₁, hn₂, hg₁, hg₂, hx12, hg₃, hne⟩ := h
  set sl := (W₁⁄L).toAffine.slope x₁ x₂ y₁ y₂ with hsl
  have hsl' : sl = (y₁ - y₂) / (x₁ - x₂) := slope_of_X_ne hx12
  set x₃ := (W₁⁄L).toAffine.addX x₁ x₂ sl with hx₃
  set y₃ := (W₁⁄L).toAffine.addY x₁ x₂ y₁ sl with hy₃
  rw [add_of_X_ne hx12] at hne
  rw [rho_some hS1 hS2 _ hg₃, rho_some hS1 hS2 hn₁ hg₁, rho_some hS1 hS2 hn₂ hg₂] at hne
  have hn₃ : (W₁⁄L).toAffine.Nonsingular x₃ y₃ := nonsingular_add hn₁ hn₂ fun hxy => hx12 hxy.left
  obtain ⟨hdX₁, hdY₁⟩ := hS1 x₁ y₁ hn₁.left hg₁
  obtain ⟨hdX₂, hdY₂⟩ := hS1 x₂ y₂ hn₂.left hg₂
  obtain ⟨hdX₃, hdY₃⟩ := hS1 x₃ y₃ hn₃.left hg₃
  set u₁ := ev L nX x₁ y₁ / ev L dX x₁ y₁ with hu₁
  set v₁ := ev L nY x₁ y₁ / ev L dY x₁ y₁ with hv₁
  set u₂ := ev L nX x₂ y₂ / ev L dX x₂ y₂ with hu₂
  set v₂ := ev L nY x₂ y₂ / ev L dY x₂ y₂ with hv₂
  set u₃ := ev L nX x₃ y₃ / ev L dX x₃ y₃ with hu₃
  set v₃ := ev L nY x₃ y₃ / ev L dY x₃ y₃ with hv₃
  have hE₁ : (W₂⁄L).toAffine.Equation u₁ v₁ := (nonsingular_rho hS1 hS2 hn₁ hg₁).left
  have hE₂ : (W₂⁄L).toAffine.Equation u₂ v₂ := (nonsingular_rho hS1 hS2 hn₂ hg₂).left
  set sl' := (W₂⁄L).toAffine.slope u₁ u₂ v₁ v₂ with hsl'def
  have hside : side3 W₁ dX dY B L (fun i => match i with
      | .x₁ => x₁ | .y₁ => y₁ | .x₂ => x₂ | .y₂ => y₂ | .l => sl
      | .u₁ => u₁ | .v₁ => v₁ | .u₂ => u₂ | .v₂ => v₂ | .u₃ => u₃ | .v₃ => v₃ | .l' => sl'
      | .w => (0 : L) | .w₂ => (0 : L) | .t₁ => (0 : L) | .t₂ => (0 : L)) ≠ 0 := by
    simp only [side3, X3, Y3]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
      (mul_ne_zero (mul_ne_zero (mul_ne_zero (sub_ne_zero.2 hx12) (gp_ne_zero_of_goodX hg₁))
      (gp_ne_zero_of_goodX hg₂)) (gp_ne_zero_of_goodX hg₃)) hdX₁) hdY₁) hdX₂) hdY₂) hdX₃) hdY₃

  set S := side3 W₁ dX dY B L (fun i => match i with
      | .x₁ => x₁ | .y₁ => y₁ | .x₂ => x₂ | .y₂ => y₂ | .l => sl
      | .u₁ => u₁ | .v₁ => v₁ | .u₂ => u₂ | .v₂ => v₂ | .u₃ => u₃ | .v₃ => v₃ | .l' => sl'
      | .w => (0 : L) | .w₂ => (0 : L) | .t₁ => (0 : L) | .t₂ => (0 : L)) with hSdef
  let z : V3 → L := fun i => match i with
      | .x₁ => x₁ | .y₁ => y₁ | .x₂ => x₂ | .y₂ => y₂ | .l => sl
      | .u₁ => u₁ | .v₁ => v₁ | .u₂ => u₂ | .v₂ => v₂ | .u₃ => u₃ | .v₃ => v₃ | .l' => sl'
      | .w => S⁻¹
      | .w₂ => if u₁ = u₂ then (v₁ - (W₂⁄L).toAffine.negY u₂ v₂)⁻¹ else (u₁ - u₂)⁻¹
      | .t₁ => (u₃ - (W₂⁄L).toAffine.addX u₁ u₂ sl')⁻¹
      | .t₂ => (v₃ - (W₂⁄L).toAffine.addY u₁ u₂ v₁ sl')⁻¹
  have hzside : side3 W₁ dX dY B L z = S := by
    simp only [hSdef, side3, X3, Y3, z]
  refine ⟨z, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · exact (equation_iff_ev L W₁ x₁ y₁).1 hn₁.left
  · exact (equation_iff_ev L W₁ x₂ y₂).1 hn₂.left
  · change sl * (x₁ - x₂) - (y₁ - y₂) = 0
    rw [hsl', div_mul_cancel₀ _ (sub_ne_zero.2 hx12), sub_self]
  · change S⁻¹ * side3 W₁ dX dY B L z - 1 = 0
    rw [hzside, inv_mul_cancel₀ hside, sub_self]
  · change u₁ * ev L dX x₁ y₁ - ev L nX x₁ y₁ = 0
    rw [hu₁, div_mul_cancel₀ _ hdX₁, sub_self]
  · change v₁ * ev L dY x₁ y₁ - ev L nY x₁ y₁ = 0
    rw [hv₁, div_mul_cancel₀ _ hdY₁, sub_self]
  · change u₂ * ev L dX x₂ y₂ - ev L nX x₂ y₂ = 0
    rw [hu₂, div_mul_cancel₀ _ hdX₂, sub_self]
  · change v₂ * ev L dY x₂ y₂ - ev L nY x₂ y₂ = 0
    rw [hv₂, div_mul_cancel₀ _ hdY₂, sub_self]
  · change u₃ * ev L dX (X3 W₁ L z) (Y3 W₁ L z) - ev L nX (X3 W₁ L z) (Y3 W₁ L z) = 0
    have hX : X3 W₁ L z = x₃ := rfl
    have hY : Y3 W₁ L z = y₃ := rfl
    rw [hX, hY, hu₃, div_mul_cancel₀ _ hdX₃, sub_self]
  · change v₃ * ev L dY (X3 W₁ L z) (Y3 W₁ L z) - ev L nY (X3 W₁ L z) (Y3 W₁ L z) = 0
    have hX : X3 W₁ L z = x₃ := rfl
    have hY : Y3 W₁ L z = y₃ := rfl
    rw [hX, hY, hv₃, div_mul_cancel₀ _ hdY₃, sub_self]

  by_cases hopp : u₁ = u₂ ∧ v₁ = (W₂⁄L).toAffine.negY u₂ v₂
  · left
    exact ⟨sub_eq_zero.2 hopp.1, sub_eq_zero.2 hopp.2⟩
  · right
    refine ⟨?_, ?_⟩
    ·
      by_cases hu : u₁ = u₂
      · have hv : v₁ ≠ (W₂⁄L).toAffine.negY u₂ v₂ := fun h => hopp ⟨hu, h⟩
        obtain ⟨hden, hslv⟩ := slope_tangent_aux hE₁ hE₂ hu hv
        right
        refine ⟨sub_eq_zero.2 hu, ?_, ?_⟩
        · change (if u₁ = u₂ then (v₁ - (W₂⁄L).toAffine.negY u₂ v₂)⁻¹ else (u₁ - u₂)⁻¹) *
            (v₁ - (W₂⁄L).toAffine.negY u₂ v₂) - 1 = 0
          rw [if_pos hu, inv_mul_cancel₀ (sub_ne_zero.2 hv), sub_self]
        · change sl' * (v₁ - (W₂⁄L).toAffine.negY u₁ v₁) - tanNum L W₂ u₁ v₁ = 0
          rw [hsl'def, hslv, div_mul_cancel₀ _ hden, sub_self]
      · left
        refine ⟨?_, ?_⟩
        · change (if u₁ = u₂ then (v₁ - (W₂⁄L).toAffine.negY u₂ v₂)⁻¹ else (u₁ - u₂)⁻¹) *
            (u₁ - u₂) - 1 = 0
          rw [if_neg hu, inv_mul_cancel₀ (sub_ne_zero.2 hu), sub_self]
        · change sl' * (u₁ - u₂) - (v₁ - v₂) = 0
          rw [hsl'def, slope_of_X_ne hu, div_mul_cancel₀ _ (sub_ne_zero.2 hu), sub_self]
    ·
      rw [add_some hopp] at hne
      have hne' : ¬ (u₃ = (W₂⁄L).toAffine.addX u₁ u₂ sl' ∧
          v₃ = (W₂⁄L).toAffine.addY u₁ u₂ v₁ sl') := fun h =>
        hne (some_eq_some L h.1 h.2)
      rcases not_and_or.1 hne' with h | h
      · left
        change (u₃ - (W₂⁄L).toAffine.addX u₁ u₂ sl')⁻¹ * (u₃ - (W₂⁄L).toAffine.addX u₁ u₂ sl') - 1 = 0
        rw [inv_mul_cancel₀ (sub_ne_zero.2 h), sub_self]
      · right
        change (v₃ - (W₂⁄L).toAffine.addY u₁ u₂ v₁ sl')⁻¹ *
          (v₃ - (W₂⁄L).toAffine.addY u₁ u₂ v₁ sl') - 1 = 0
        rw [inv_mul_cancel₀ (sub_ne_zero.2 h), sub_self]

end Sys3

section Transfers

variable [IsAlgClosed k₀] [DecidableEq k₀]
variable (k : Type*) [Field k] [Algebra F k] [Algebra k₀ k] [IsScalarTower F k₀ k] [DecidableEq k]
variable {W₁ W₂ nX dX nY dY B}
variable [W₁.IsElliptic] [W₂.IsElliptic]

theorem S1_transfer (h₀ : S1 W₁ dX dY B k₀) : S1 W₁ dX dY B k := by
  by_contra h
  obtain ⟨z, hz⟩ := exists_sem1_of_not_S1 h
  rw [Formula.sem_congr (fun i => (atoms1_aeval W₁ dX dY B k z i).symm)] at hz
  obtain ⟨z₀, hz₀⟩ := Formula.transfer _ _ z hz
  rw [Formula.sem_congr (fun i => atoms1_aeval W₁ dX dY B k₀ z₀ i)] at hz₀
  exact not_S1_of_sem1 z₀ hz₀ h₀

theorem S2_transfer (h₀ : S2 W₁ W₂ nX dX nY dY B k₀) : S2 W₁ W₂ nX dX nY dY B k := by
  by_contra h
  obtain ⟨z, hz⟩ := exists_sem2_of_not_S2 h
  rw [Formula.sem_congr (fun i => (atoms2_aeval W₁ W₂ nX dX nY dY B k z i).symm)] at hz
  obtain ⟨z₀, hz₀⟩ := Formula.transfer _ _ z hz
  rw [Formula.sem_congr (fun i => atoms2_aeval W₁ W₂ nX dX nY dY B k₀ z₀ i)] at hz₀
  exact not_S2_of_sem2 z₀ hz₀ h₀

theorem GEN_transfer (h₁ : S1 W₁ dX dY B k₀) (h₂ : S2 W₁ W₂ nX dX nY dY B k₀)
    (h₀ : GEN W₁ W₂ nX dX nY dY B k₀) : GEN W₁ W₂ nX dX nY dY B k := by
  by_contra h
  obtain ⟨z, hz⟩ := exists_sem3_of_not_GEN (S1_transfer k h₁) (S2_transfer k h₂) h
  rw [Formula.sem_congr (fun i => (atoms3_aeval W₁ W₂ nX dX nY dY B k z i).symm)] at hz
  obtain ⟨z₀, hz₀⟩ := Formula.transfer _ _ z hz
  rw [Formula.sem_congr (fun i => atoms3_aeval W₁ W₂ nX dX nY dY B k₀ z₀ i)] at hz₀
  exact not_GEN_of_sem3 h₁ h₂ z₀ hz₀ h₀

end Transfers

end Systems

section Extend

variable {G H : Type*} [AddCommGroup G] [AddCommGroup H] [Infinite G]
variable (ρ : G → H) (Bad : Set G) (Coll : G → G → Prop)

structure ExtData : Prop where
  bad_finite : Bad.Finite
  coll_finite : ∀ P, {Q | Coll P Q}.Finite
  coll_symm : ∀ P Q, Coll P Q → Coll Q P
  add : ∀ P Q, P ∉ Bad → Q ∉ Bad → P + Q ∉ Bad → ¬ Coll P Q → ρ (P + Q) = ρ P + ρ Q

variable {ρ Bad Coll}

theorem exists_notMem_of_finite {S : Set G} (hS : S.Finite) : ∃ R, R ∉ S :=
  hS.infinite_compl.nonempty

theorem finite_preimage_add (S : Set G) (hS : S.Finite) (P : G) :
    {R | P + R ∈ S}.Finite :=
  hS.preimage (add_right_injective P).injOn

theorem ExtData.indep (hD : ExtData ρ Bad Coll) (P R R' : G) (hR : R ∉ Bad) (hPR : P + R ∉ Bad)
    (hR' : R' ∉ Bad) (hPR' : P + R' ∉ Bad) :
    ρ (P + R) - ρ R = ρ (P + R') - ρ R' := by
  have hfin : (Bad ∪ {S | P + S ∈ Bad} ∪ {S | P + R + S ∈ Bad} ∪ {S | P + R' + S ∈ Bad} ∪
      {S | Coll (P + R) S} ∪ {S | Coll (P + R') S} ∪ {S | Coll R (P + S)} ∪
      {S | Coll R' (P + S)}).Finite := by
    refine ((((((hD.bad_finite.union (finite_preimage_add _ hD.bad_finite _)).union
      (finite_preimage_add _ hD.bad_finite _)).union (finite_preimage_add _ hD.bad_finite _)).union
      (hD.coll_finite _)).union (hD.coll_finite _)).union ?_).union ?_
    · exact (hD.coll_finite R).preimage (add_right_injective P).injOn
    · exact (hD.coll_finite R').preimage (add_right_injective P).injOn
  obtain ⟨S, hS⟩ := exists_notMem_of_finite hfin
  simp only [Set.mem_union, Set.mem_setOf_eq, not_or] at hS
  obtain ⟨⟨⟨⟨⟨⟨⟨hS1, hS2⟩, hS3⟩, hS4⟩, hS5⟩, hS6⟩, hS7⟩, hS8⟩ := hS
  have key : ∀ T, T ∉ Bad → P + T ∉ Bad → P + T + S ∉ Bad → ¬ Coll (P + T) S →
      ¬ Coll T (P + S) → ρ (P + T) - ρ T = ρ (P + S) - ρ S := by
    intro T hT hPT hPTS hc1 hc2
    have e1 := hD.add (P + T) S hPT hS1 hPTS hc1
    have e2 := hD.add T (P + S) hT hS2 (by rwa [show T + (P + S) = P + T + S by abel]) hc2
    rw [show T + (P + S) = P + T + S by abel] at e2
    rw [e2] at e1

    rw [sub_eq_sub_iff_add_eq_add, ← e1, add_comm]
  rw [key R hR hPR hS3 hS5 hS7, key R' hR' hPR' hS4 hS6 hS8]

theorem ExtData.exists_aux (hD : ExtData ρ Bad Coll) (P : G) : ∃ R, R ∉ Bad ∧ P + R ∉ Bad := by
  obtain ⟨R, hR⟩ := exists_notMem_of_finite
    (hD.bad_finite.union (finite_preimage_add _ hD.bad_finite P))
  simp only [Set.mem_union, Set.mem_setOf_eq, not_or] at hR
  exact ⟨R, hR.1, hR.2⟩

noncomputable def ExtData.ext (hD : ExtData ρ Bad Coll) : G →+ H :=
  AddMonoidHom.mk' (fun P => ρ (P + (hD.exists_aux P).choose) - ρ (hD.exists_aux P).choose)
    (by
      intro P Q
      obtain ⟨R, hR⟩ := exists_notMem_of_finite ((hD.bad_finite.union
        (finite_preimage_add _ hD.bad_finite (P + Q))).union
        (finite_preimage_add _ hD.bad_finite Q))
      simp only [Set.mem_union, Set.mem_setOf_eq, not_or] at hR
      obtain ⟨⟨hR1, hR2⟩, hR3⟩ := hR
      have ePQ := hD.indep (P + Q) _ R (hD.exists_aux (P + Q)).choose_spec.1
        (hD.exists_aux (P + Q)).choose_spec.2 hR1 hR2
      have eQ := hD.indep Q _ R (hD.exists_aux Q).choose_spec.1
        (hD.exists_aux Q).choose_spec.2 hR1 hR3
      have eP := hD.indep P _ (Q + R) (hD.exists_aux P).choose_spec.1
        (hD.exists_aux P).choose_spec.2 hR3 (by rwa [← add_assoc])
      rw [ePQ, eQ, eP, ← add_assoc]
      abel)

theorem ExtData.ext_apply_of_notMem (hD : ExtData ρ Bad Coll) {P : G} (hP : P ∉ Bad) :
    hD.ext P = ρ P := by
  obtain ⟨R, hR⟩ := exists_notMem_of_finite ((hD.bad_finite.union
    (finite_preimage_add _ hD.bad_finite P)).union (hD.coll_finite P))
  simp only [Set.mem_union, Set.mem_setOf_eq, not_or] at hR
  obtain ⟨⟨hR1, hR2⟩, hR3⟩ := hR
  change ρ (P + (hD.exists_aux P).choose) - ρ (hD.exists_aux P).choose = ρ P
  rw [hD.indep P _ R (hD.exists_aux P).choose_spec.1 (hD.exists_aux P).choose_spec.2 hR1 hR2,
    hD.add P R hP hR1 hR2 hR3, add_sub_cancel_right]

end Extend

section Points

variable {F : Type*} [Field F] (L : Type*) [Field L] [Algebra F L] (W : WeierstrassCurve F)

theorem finite_setOf_equation (x : L) : {y : L | (W⁄L).toAffine.Equation x y}.Finite := by
  have hne : ((W⁄L).toAffine.polynomial.map (evalRingHom x)) ≠ 0 :=
    (WeierstrassCurve.Affine.monic_polynomial.map _).ne_zero
  refine (Polynomial.finite_setOf_isRoot hne).subset ?_
  intro y hy
  simp only [Set.mem_setOf_eq, IsRoot.def, map_evalRingHom_eval]
  exact hy

theorem finite_setOf_X_eq (c : L) :
    {P : (W⁄L).Point | ∃ x y h, P = .some x y h ∧ x = c}.Finite := by
  have hfin : (⋃ y ∈ {y : L | (W⁄L).toAffine.Equation c y},
      {P : (W⁄L).Point | ∃ h : (W⁄L).toAffine.Nonsingular c y, P = .some c y h}).Finite := by
    refine Set.Finite.biUnion (finite_setOf_equation L W c) fun y _ => ?_
    refine Set.Subsingleton.finite ?_
    rintro P ⟨h1, rfl⟩ Q ⟨h2, rfl⟩
    rfl
  refine hfin.subset ?_
  rintro P ⟨x, y, h, rfl, rfl⟩
  simp only [Set.mem_iUnion, Set.mem_setOf_eq]
  exact ⟨y, h.left, h, rfl⟩

theorem infinite_point [IsAlgClosed L] [W.IsElliptic] : Infinite (W⁄L).Point := by
  haveI := isElliptic_baseChange L W
  have hy : ∀ x : L, ∃ y : L, (W⁄L).toAffine.Nonsingular x y := by
    intro x
    have hdeg : ((W⁄L).toAffine.polynomial.map (evalRingHom x)).degree ≠ 0 := by
      rw [WeierstrassCurve.Affine.monic_polynomial.degree_map,
        WeierstrassCurve.Affine.degree_polynomial]
      norm_num
    obtain ⟨y, hy⟩ := IsAlgClosed.exists_root _ hdeg
    refine ⟨y, ((W⁄L).toAffine.equation_iff_nonsingular).mp ?_⟩
    rw [IsRoot.def, map_evalRingHom_eval] at hy
    exact hy
  choose f hf using hy
  refine Infinite.of_injective (fun x : L => (Point.some x (f x) (hf x) : (W⁄L).Point)) ?_
  intro x x' hxx'
  exact (Point.some.inj hxx').left

theorem eq_top_of_finite_compl {G : Type*} [AddCommGroup G] [Infinite G] (H : AddSubgroup G)
    (hH : ((H : Set G)ᶜ).Finite) : H = ⊤ := by
  by_contra hne
  obtain ⟨a, ha⟩ : ∃ a, a ∉ H := by
    by_contra hall
    push Not at hall
    exact hne ((AddSubgroup.eq_top_iff' H).mpr hall)
  have hsub : (fun h : G => a + h) '' (H : Set G) ⊆ (H : Set G)ᶜ := by
    rintro _ ⟨h, hh, rfl⟩ hah
    have : a + h - h ∈ H := H.sub_mem hah hh
    exact ha (by simpa using this)
  have hHfin : (H : Set G).Finite :=
    (hH.subset hsub).of_finite_image (add_right_injective a).injOn
  have huniv : (Set.univ : Set G).Finite := by
    rw [← Set.union_compl_self (H : Set G)]
    exact hHfin.union hH
  exact Set.infinite_univ huniv

end Points

section Main

variable {F : Type*} [Field F] {k₀ : Type*} {k : Type*} [Field k₀] [Field k] [Algebra F k₀]
  [Algebra F k] [Algebra k₀ k] [IsScalarTower F k₀ k] [IsAlgClosed k₀] [DecidableEq k₀]
  [DecidableEq k] (W₁ W₂ : WeierstrassCurve F) [W₁.IsElliptic] [W₂.IsElliptic]

local notation "ι" => IsScalarTower.toAlgHom F k₀ k

theorem algebraMap_eq_ι (x : k₀) : algebraMap k₀ k x = (ι) x := rfl

theorem main_of_rep {α₀ : (W₁⁄k₀).Point →+ (W₂⁄k₀).Point}
    (hα₀ : IsRationallyRepresented k₀ W₁ W₂ α₀) :
    ∃ α ∈ WeierstrassCurve.rationalHomSet k W₁ W₂,
      ∀ P : (W₁⁄k₀).Point, α (Point.map ι P) = Point.map ι (α₀ P) := by
  obtain ⟨nX, dX, nY, dY, B₀, hB₀, hrep⟩ := hα₀
  set B : Finset k₀ := hB₀.toFinset with hBdef
  have hgood₀ : ∀ {x : k₀}, GoodX B k₀ x ↔ x ∉ B₀ := by
    intro x
    simp only [GoodX, hBdef, Set.Finite.mem_toFinset, Algebra.algebraMap_self, RingHom.id_apply]
    exact ⟨fun h hx => h x hx rfl, fun h b hb hxb => h (hxb ▸ hb)⟩

  have hrho₀ : ∀ {x y : k₀} (h : (W₁⁄k₀).toAffine.Nonsingular x y), x ∉ B₀ →
      rho k₀ W₁ W₂ nX dX nY dY (.some x y h) = α₀ (.some x y h) := by
    intro x y h hx
    obtain ⟨-, -, h', e⟩ := hrep x y h hx
    rw [e]
    exact rho_some_of k₀ W₁ W₂ nX dX nY dY h h'

  have hS1₀ : S1 W₁ dX dY B k₀ := by
    intro x y hxy hg
    obtain ⟨h1, h2, -⟩ := hrep x y (nonsingular_of_equation k₀ W₁ hxy) (hgood₀.1 hg)
    exact ⟨h1, h2⟩
  have hS2₀ : S2 W₁ W₂ nX dX nY dY B k₀ := by
    intro x y hxy hg _ _
    obtain ⟨-, -, h', -⟩ := hrep x y (nonsingular_of_equation k₀ W₁ hxy) (hgood₀.1 hg)
    exact h'.left
  have hGEN₀ : GEN W₁ W₂ nX dX nY dY B k₀ := by
    intro x₁ y₁ x₂ y₂ h₁ h₂ hg₁ hg₂ hx12 hg₃
    rw [add_of_X_ne hx12, hrho₀ _ (hgood₀.1 hg₃), hrho₀ h₁ (hgood₀.1 hg₁),
      hrho₀ h₂ (hgood₀.1 hg₂), ← add_of_X_ne hx12, map_add]

  have hS1 : S1 W₁ dX dY B k := S1_transfer k hS1₀
  have hS2 : S2 W₁ W₂ nX dX nY dY B k := S2_transfer k hS2₀
  have hGEN : GEN W₁ W₂ nX dX nY dY B k := GEN_transfer k hS1₀ hS2₀ hGEN₀

  haveI : Infinite (W₁⁄k₀).Point := infinite_point k₀ W₁
  haveI : Infinite (W₁⁄k).Point :=
    Infinite.of_injective (Point.map ι) (Point.map_injective (W' := W₁) ι)
  let Good : (W₁⁄k).Point → Prop := fun P =>
    ∃ (x y : k) (h : (W₁⁄k).toAffine.Nonsingular x y), P = .some x y h ∧ GoodX B k x
  let Bad : Set (W₁⁄k).Point := {P | ¬ Good P}
  let Coll : (W₁⁄k).Point → (W₁⁄k).Point → Prop := fun P Q =>
    ∃ (x₁ y₁ : k) (h₁ : (W₁⁄k).toAffine.Nonsingular x₁ y₁) (x₂ y₂ : k)
      (h₂ : (W₁⁄k).toAffine.Nonsingular x₂ y₂), P = .some x₁ y₁ h₁ ∧ Q = .some x₂ y₂ h₂ ∧ x₁ = x₂
  have hBad : Bad.Finite := by
    have hfin : (insert (0 : (W₁⁄k).Point)
        (⋃ b ∈ (B : Set k₀), {P : (W₁⁄k).Point | ∃ x y h, P = .some x y h ∧ x = (ι) b})).Finite :=
      Set.Finite.insert _ (Set.Finite.biUnion B.finite_toSet fun b _ => finite_setOf_X_eq k W₁ _)
    refine hfin.subset ?_
    intro P hP
    change ¬ Good P at hP
    rcases P with _ | ⟨x, y, h⟩
    · exact Set.mem_insert _ _
    · refine Set.mem_insert_of_mem _ ?_
      simp only [Set.mem_iUnion, Set.mem_setOf_eq, Finset.mem_coe]
      have : ¬ GoodX B k x := fun hg => hP ⟨x, y, h, rfl, hg⟩
      simp only [GoodX, not_forall, not_not, exists_prop] at this
      obtain ⟨b, hb, hxb⟩ := this
      exact ⟨b, hb, x, y, h, rfl, hxb⟩
  have hD : ExtData (rho k W₁ W₂ nX dX nY dY) Bad Coll := by
    refine ⟨hBad, ?_, ?_, ?_⟩
    · intro P
      rcases P with _ | ⟨x₁, y₁, h₁⟩
      · convert Set.finite_empty
        ext Q
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, Coll]
        rintro ⟨_, _, _, _, _, _, h, -⟩
        exact (some_ne_zero _ h.symm).elim
      · refine (finite_setOf_X_eq k W₁ x₁).subset ?_
        rintro Q ⟨x, y, h, x', y', h', hP, hQ, hxx'⟩
        obtain ⟨rfl, -⟩ := Point.some.inj hP
        exact ⟨x', y', h', hQ, hxx'.symm⟩
    · rintro P Q ⟨x₁, y₁, h₁, x₂, y₂, h₂, rfl, rfl, hx⟩
      exact ⟨x₂, y₂, h₂, x₁, y₁, h₁, rfl, rfl, hx.symm⟩
    · intro P Q hP hQ hPQ hc
      simp only [Bad, Set.mem_setOf_eq, not_not] at hP hQ hPQ
      obtain ⟨x₁, y₁, h₁, rfl, hg₁⟩ := hP
      obtain ⟨x₂, y₂, h₂, rfl, hg₂⟩ := hQ
      have hx12 : x₁ ≠ x₂ := fun h => hc ⟨x₁, y₁, h₁, x₂, y₂, h₂, rfl, rfl, h⟩
      obtain ⟨x₃, y₃, h₃, e₃, hg₃⟩ := hPQ
      rw [add_of_X_ne hx12] at e₃
      obtain ⟨rfl, -⟩ := Point.some.inj e₃
      exact hGEN x₁ y₁ x₂ y₂ h₁ h₂ hg₁ hg₂ hx12 hg₃

  refine ⟨hD.ext, Or.inr ⟨nX, dX, nY, dY, (ι) '' (B : Set k₀), B.finite_toSet.image _, ?_⟩, ?_⟩
  ·
    intro x y h hx
    have hg : GoodX B k x := by
      intro b hb hxb
      exact hx ⟨b, hb, by rw [hxb]; rfl⟩
    obtain ⟨hdX, hdY⟩ := hS1 x y h.left hg
    refine ⟨hdX, hdY, nonsingular_rho hS1 hS2 h hg, ?_⟩
    rw [hD.ext_apply_of_notMem (by exact fun hb => hb ⟨x, y, h, rfl, hg⟩)]
    exact rho_some hS1 hS2 h hg
  ·
    suffices hEq : (hD.ext.comp (Point.map (W' := W₁) ι)).eqLocus ((Point.map (W' := W₂) ι).comp α₀) = ⊤ by
      intro P
      have := (AddSubgroup.eq_top_iff' _).1 hEq P
      simpa [AddMonoidHom.eqLocus] using this
    apply eq_top_of_finite_compl
    have hfin : (insert (0 : (W₁⁄k₀).Point)
        (⋃ b ∈ B₀, {P : (W₁⁄k₀).Point | ∃ x y h, P = .some x y h ∧ x = b})).Finite :=
      Set.Finite.insert _ (Set.Finite.biUnion hB₀ fun b _ => finite_setOf_X_eq k₀ W₁ _)
    refine hfin.subset ?_
    intro P hP
    rw [Set.mem_compl_iff, SetLike.mem_coe] at hP
    rcases P with _ | ⟨x, y, h⟩
    · exact Set.mem_insert _ _
    · refine Set.mem_insert_of_mem _ ?_
      simp only [Set.mem_iUnion, Set.mem_setOf_eq]
      by_contra hxB
      push Not at hxB
      have hxB₀ : x ∉ B₀ := fun hb => hxB x hb x y h rfl rfl
      apply hP
      change hD.ext (Point.map ι (.some x y h)) = Point.map ι (α₀ (.some x y h))
      have hgx : GoodX B k ((ι) x) := by
        intro b hb hxb
        have hxb' : x = b := (ι).injective hxb
        exact hxB₀ (hxb' ▸ (Set.Finite.mem_toFinset hB₀).1 hb)
      obtain ⟨hdX₀, hdY₀, h', e⟩ := hrep x y h hxB₀
      rw [Point.map_some, hD.ext_apply_of_notMem (by exact fun hb => hb ⟨_, _, _, rfl, hgx⟩),
        rho_some hS1 hS2 _ hgx, e, Point.map_some]
      refine some_eq_some k ?_ ?_
      · change ev k nX ((ι) x) ((ι) y) / ev k dX ((ι) x) ((ι) y) = (ι) (ev k₀ nX x y / ev k₀ dX x y)
        rw [map_div₀, map_ev, map_ev]
      · change ev k nY ((ι) x) ((ι) y) / ev k dY ((ι) x) ((ι) y) = (ι) (ev k₀ nY x y / ev k₀ dY x y)
        rw [map_div₀, map_ev, map_ev]

theorem main {α₀ : (W₁⁄k₀).Point →+ (W₂⁄k₀).Point}
    (hα₀ : α₀ ∈ WeierstrassCurve.rationalHomSet k₀ W₁ W₂) :
    ∃ α ∈ WeierstrassCurve.rationalHomSet k W₁ W₂,
      ∀ P : (W₁⁄k₀).Point, α (Point.map ι P) = Point.map ι (α₀ P) := by
  rcases hα₀ with rfl | hα₀
  · exact ⟨0, zero_mem_rationalHomSet k W₁ W₂, fun P => by simp⟩
  · exact main_of_rep W₁ W₂ hα₀

end Main

end WeierstrassCurve.RatHomExtend

open _root_.WeierstrassCurve _root_.P2MW.S_WeierstrassCurve_exists_mem_rationalHomSet_apply_map_eq_map_apply.WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point in
theorem solution {F : Type*} [Field F] (k₀ : Type*) (k : Type*) [Field k₀] [Field k] [Algebra F k₀] [Algebra F k] [Algebra k₀ k] [IsScalarTower F k₀ k] [IsAlgClosed k₀] [DecidableEq k₀] [DecidableEq k] (W₁ W₂ : WeierstrassCurve F) [W₁.IsElliptic] [W₂.IsElliptic] {α₀ : (W₁⁄k₀).Point →+ (W₂⁄k₀).Point} (hα₀ : α₀ ∈ WeierstrassCurve.rationalHomSet k₀ W₁ W₂) : ∃ α ∈ WeierstrassCurve.rationalHomSet k W₁ W₂, ∀ P : (W₁⁄k₀).Point, α (WeierstrassCurve.Affine.Point.map (IsScalarTower.toAlgHom F k₀ k) P) = WeierstrassCurve.Affine.Point.map (IsScalarTower.toAlgHom F k₀ k) (α₀ P) :=
  WeierstrassCurve.RatHomExtend.main W₁ W₂ hα₀

end S_WeierstrassCurve_exists_mem_rationalHomSet_apply_map_eq_map_apply
end P2MW
export P2MW.S_WeierstrassCurve_exists_mem_rationalHomSet_apply_map_eq_map_apply (solution)
