-- Prove2me | solution 1 for PhilipponMultiplicity.closure_action_has_filtered_twist_model
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-09T01:24:34.474982+00:00
-- url     : https://prove2.me/submissions/a51796ac-ef77-4a1d-be4e-f98a2e3caba9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_PhilipponMultiplicity_closure_action_has_coherent_generator_presentation
import Definitions.Def_PhilipponMultiplicity_SectionThree
import Definitions.Def_PhilipponMultiplicity_Support
import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
import Mathlib.LinearAlgebra.Quotient.Basic


section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace PhilipponMultiplicity.FilteredEuler

section Descent
variable {R L A C : Type*} [Ring R] [AddCommGroup L] [Module R L]
  [AddCommGroup A] [Module R A] [AddCommGroup C] [Module R C]

/-- Descent of a function through a surjection. -/
def descend (q : L →ₗ[R] A) (hq : Function.Surjective q) (f : L → C) : A → C :=
  fun a => f (hq a).choose

omit [AddCommGroup C] [Module R C] in
theorem descend_apply (q : L →ₗ[R] A) (hq : Function.Surjective q) (f : L → C)
    (hf : ∀ x y, q x = q y → f x = f y) (x : L) :
    descend q hq f (q x) = f x :=
  hf _ x (hq (q x)).choose_spec

theorem constant_on_fibers (q : L →ₗ[R] A) (f : L →ₗ[R] C)
    (hf : ∀ x, q x = 0 → f x = 0) :
    ∀ x y, q x = q y → f x = f y := by
  intro x y h
  apply sub_eq_zero.mp
  rw [← map_sub]
  exact hf _ (by simpa using sub_eq_zero.mpr h)

def linearDescend (q : L →ₗ[R] A) (hq : Function.Surjective q) (f : L →ₗ[R] C)
    (hf : ∀ x, q x = 0 → f x = 0) : A →ₗ[R] C where
  toFun := descend q hq f
  map_add' a b := by
    obtain ⟨x, rfl⟩ := hq a
    obtain ⟨y, rfl⟩ := hq b
    rw [← map_add, descend_apply q hq f (constant_on_fibers q f hf),
      descend_apply q hq f (constant_on_fibers q f hf),
      descend_apply q hq f (constant_on_fibers q f hf), map_add]
  map_smul' r a := by
    obtain ⟨x, rfl⟩ := hq a
    change descend q hq f (r • q x) = r • descend q hq f (q x)
    rw [← q.map_smul, descend_apply q hq f (constant_on_fibers q f hf),
      descend_apply q hq f (constant_on_fibers q f hf), f.map_smul]

@[simp] theorem linearDescend_apply (q : L →ₗ[R] A) (hq : Function.Surjective q)
    (f : L →ₗ[R] C) (hf : ∀ x, q x = 0 → f x = 0) (x : L) :
    linearDescend q hq f hf (q x) = f x :=
  descend_apply q hq f (constant_on_fibers q f hf) x

end Descent

section Action
variable {T L A : Type*} [Group T] [AddCommGroup L] [Module ℤ L]
  [AddCommGroup A] [Module ℤ A]
  (q : L →ₗ[ℤ] A) (hq : Function.Surjective q)
  (ρ : T →* (L ≃ₗ[ℤ] L))
  (hker : ∀ g x, q x = 0 → q (ρ g x) = 0)

def actionMap (g : T) : A →ₗ[ℤ] A :=
  linearDescend q hq (q.comp (ρ g).toLinearMap) (hker g)

@[simp] theorem actionMap_apply (g : T) (x : L) :
    actionMap q hq ρ hker g (q x) = q (ρ g x) :=
  linearDescend_apply _ _ _ _ _

theorem actionMap_one (a : A) : actionMap q hq ρ hker 1 a = a := by
  obtain ⟨x, rfl⟩ := hq a
  simp

theorem actionMap_mul (g h : T) (a : A) :
    actionMap q hq ρ hker (g * h) a =
      actionMap q hq ρ hker g (actionMap q hq ρ hker h a) := by
  obtain ⟨x, rfl⟩ := hq a
  simp

/-- A kernel-invariant action descends to genuine automorphisms of the quotient. -/
def actionEquiv (g : T) : A ≃ₗ[ℤ] A :=
  { actionMap q hq ρ hker g with
    invFun := actionMap q hq ρ hker g⁻¹
    left_inv := fun a => by
      change actionMap q hq ρ hker g⁻¹ (actionMap q hq ρ hker g a) = a
      rw [← actionMap_mul, inv_mul_cancel, actionMap_one]
    right_inv := fun a => by
      change actionMap q hq ρ hker g (actionMap q hq ρ hker g⁻¹ a) = a
      rw [← actionMap_mul, mul_inv_cancel, actionMap_one] }

def quotientAction : T →* (A ≃ₗ[ℤ] A) where
  toFun := actionEquiv q hq ρ hker
  map_one' := by ext a; exact actionMap_one q hq ρ hker a
  map_mul' g h := by ext a; exact actionMap_mul q hq ρ hker g h a

@[simp] theorem quotientAction_apply (g : T) (x : L) :
    quotientAction q hq ρ hker g (q x) = q (ρ g x) :=
  actionMap_apply q hq ρ hker g x

end Action

section Twists
variable {L B : Type*} [AddCommGroup L] [AddCommGroup B] [Module ℤ B]
  (β : Multiplicative L →* (B ≃ₗ[ℤ] B))

def twist (x : L) : B →ₗ[ℤ] B := (β (Multiplicative.ofAdd x)).toLinearMap

@[simp] theorem twist_zero (b : B) : twist β 0 b = b := by simp [twist]

theorem twist_add (x y : L) (b : B) :
    twist β (x + y) b = twist β x (twist β y b) := by
  change β (Multiplicative.ofAdd x * Multiplicative.ofAdd y) b = _
  rw [map_mul]
  rfl

def difference (y : L) : B →ₗ[ℤ] B := twist β y - LinearMap.id

theorem difference_nilpotent (F : ℕ → Submodule ℤ B) (hzero : F 0 = ⊥)
    (hdrop : ∀ n y b, b ∈ F (n + 1) → difference β y b ∈ F n)
    (n : ℕ) (y : L) (b : B) (hb : b ∈ F n) :
    (difference β y)^[n] b = 0 := by
  induction n generalizing b with
  | zero => simpa [hzero] using hb
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    exact ih (difference β y b) (hdrop n y b hb)

/-- Forward differences of Euler functions are induced by the twist-minus-identity operator. -/
theorem iterate_euler (χ : B →ₗ[ℤ] ℚ) (n : ℕ) (y x : L) (b : B) :
    (fwdDiff y)^[n] (fun z => χ (twist β z b)) x =
      χ (twist β x ((difference β y)^[n] b)) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', fwdDiff]
    rw [ih, ih, twist_add]
    rw [Function.iterate_succ_apply', difference, LinearMap.sub_apply,
      LinearMap.id_apply, map_sub, map_sub]

theorem euler_bound (χ : B →ₗ[ℤ] ℚ) (F : ℕ → Submodule ℤ B) (hzero : F 0 = ⊥)
    (hdrop : ∀ n y b, b ∈ F (n + 1) → difference β y b ∈ F n)
    (n : ℕ) (b : B) (hb : b ∈ F n) (y : L) :
    (fwdDiff y)^[n] (fun x => χ (twist β x b)) = 0 := by
  ext x
  rw [iterate_euler, difference_nilpotent β F hzero hdrop n y b hb, map_zero, map_zero]
  rfl

end Twists

section EulerDescent
variable {L A B : Type*} [AddCommGroup L] [Module ℤ L]
  [AddCommGroup A] [Module ℤ A] [AddCommGroup B] [Module ℤ B]
  (q : L →ₗ[ℤ] A) (hq : Function.Surjective q)
  (β : Multiplicative L →* (B ≃ₗ[ℤ] B)) (χ : B →ₗ[ℤ] ℚ)
  (hχ : ∀ l, q l = 0 → ∀ b, χ (twist β l b) = χ b)

include hχ in
theorem euler_constant_on_fibers (b : B) (x y : L) (h : q x = q y) :
    χ (twist β x b) = χ (twist β y b) := by
  have hk : q (x - y) = 0 := by rw [map_sub, h, sub_self]
  calc
    χ (twist β x b) = χ (twist β (x - y) (twist β y b)) := by
      rw [← twist_add, sub_add_cancel]
    _ = χ (twist β y b) := hχ _ hk _

def eulerFunction (b : B) : A → ℚ := descend q hq (fun x => χ (twist β x b))

include hχ in
@[simp] theorem eulerFunction_apply (b : B) (x : L) :
    eulerFunction q hq β χ b (q x) = χ (twist β x b) :=
  descend_apply q hq _ (euler_constant_on_fibers q β χ hχ b) x

theorem iterate_pullback (f : A → ℚ) (n : ℕ) (y x : L) :
    (fwdDiff y)^[n] (fun z => f (q z)) x = (fwdDiff (q y))^[n] f (q x) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', fwdDiff, fwdDiff,
      ih, ih, map_add]

include hχ in
theorem quotient_euler_bound (F : ℕ → Submodule ℤ B) (hzero : F 0 = ⊥)
    (hdrop : ∀ n y b, b ∈ F (n + 1) → difference β y b ∈ F n)
    (n : ℕ) (b : B) (hb : b ∈ F n) (a : A) :
    (fwdDiff a)^[n] (eulerFunction q hq β χ b) = 0 := by
  obtain ⟨y, rfl⟩ := hq a
  ext z
  obtain ⟨x, rfl⟩ := hq z
  rw [← iterate_pullback q]
  have he : (fun z => eulerFunction q hq β χ b (q z)) =
      (fun z => χ (twist β z b)) := by
    funext z
    exact eulerFunction_apply q hq β χ hχ b z
  rw [he, euler_bound β χ F hzero hdrop n b hb y]
  rfl

end EulerDescent
end PhilipponMultiplicity.FilteredEuler
end

end


section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators
noncomputable section

namespace PhilipponMultiplicity.CoherentPresentation
variable {T C : Type*} [Group T]

/-- Permutations of generators act linearly on the free integer module. -/
def freeAction (σ : T →* Equiv.Perm C) : T →* ((C →₀ ℤ) ≃ₗ[ℤ] (C →₀ ℤ)) where
  toFun l := Finsupp.domLCongr (σ l)
  map_one' := by
    rw [map_one]
    exact Finsupp.domLCongr_refl
  map_mul' g h := by
    apply LinearEquiv.toLinearMap_injective
    apply Finsupp.lhom_ext
    intro a n
    simp

@[simp] theorem freeAction_single (σ : T →* Equiv.Perm C) (l : T) (a : C) (n : ℤ) :
    freeAction σ l (Finsupp.single a n) = Finsupp.single (σ l a) n := by
  exact Finsupp.domLCongr_single _ _ _

theorem freeAction_eq_lmapDomain (σ : T →* Equiv.Perm C) (l : T) (v : C →₀ ℤ) :
    freeAction σ l v = Finsupp.lmapDomain ℤ ℤ (σ l) v := by
  simp [freeAction, Finsupp.domCongr_apply, Finsupp.equivMapDomain_eq_mapDomain]

variable (R : Submodule ℤ (C →₀ ℤ))

abbrev PresentedGroup := (C →₀ ℤ) ⧸ R

def generator (a : C) : PresentedGroup R := R.mkQ (Finsupp.single a 1)

def level (d : C → ℕ) (n : ℕ) : Submodule ℤ (PresentedGroup R) :=
  Submodule.span ℤ {b | ∃ a, d a < n ∧ b = generator R a}

theorem level_zero (d : C → ℕ) : level R d 0 = ⊥ := by
  simp [level]

theorem generator_mem_level (d : C → ℕ) (n : ℕ) (a : C) (ha : d a < n) :
    generator R a ∈ level R d n :=
  Submodule.subset_span ⟨a, ha, rfl⟩

theorem mkQ_mem_level (d : C → ℕ) (n : ℕ) (w : C →₀ ℤ)
    (hw : ∀ a ∈ w.support, d a < n) : R.mkQ w ∈ level R d n := by
  classical
  have he : R.mkQ w = ∑ a ∈ w.support, (w a) • generator R a := by
    conv_lhs => rw [← Finsupp.sum_single w]
    simp only [Finsupp.sum, map_sum, generator, ← map_smul, Finsupp.smul_single_one]
  rw [he]
  exact Submodule.sum_mem _ (fun a ha =>
    Submodule.smul_mem _ _ (generator_mem_level R d n a (hw a ha)))

variable (σ : T →* Equiv.Perm C)
  (hR : ∀ l v, v ∈ R → Finsupp.lmapDomain ℤ ℤ (σ l) v ∈ R)

include hR in
theorem action_preserves_kernel :
    ∀ l v, R.mkQ v = 0 → R.mkQ (freeAction σ l v) = 0 := by
  intro l v hv
  simp only [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hv ⊢
  rw [freeAction_eq_lmapDomain]
  exact hR l v hv

def quotientAction : T →* (PresentedGroup R ≃ₗ[ℤ] PresentedGroup R) :=
  FilteredEuler.quotientAction R.mkQ R.mkQ_surjective (freeAction σ)
    (action_preserves_kernel R σ hR)

@[simp] theorem quotientAction_mkQ (l : T) (v : C →₀ ℤ) :
    quotientAction R σ hR l (R.mkQ v) = R.mkQ (freeAction σ l v) :=
  FilteredEuler.quotientAction_apply _ _ _ _ _ _

@[simp] theorem quotientAction_generator (l : T) (a : C) :
    quotientAction R σ hR l (generator R a) = generator R (σ l a) := by
  rw [generator, quotientAction_mkQ, freeAction_single]
  rfl

theorem generator_difference (d : C → ℕ)
    (hdrop : ∀ l a, ∃ w : C →₀ ℤ,
      (∀ b ∈ w.support, d b < d a) ∧
      Finsupp.single (σ l a) 1 - Finsupp.single a 1 - w ∈ R)
    (n : ℕ) (l : T) (a : C) (ha : d a < n + 1) :
    quotientAction R σ hR l (generator R a) - generator R a ∈ level R d n := by
  obtain ⟨w, hw, hr⟩ := hdrop l a
  have he : quotientAction R σ hR l (generator R a) - generator R a = R.mkQ w := by
    apply sub_eq_zero.mp
    rw [quotientAction_generator, generator, generator, ← map_sub, ← map_sub]
    exact (Submodule.Quotient.mk_eq_zero R).mpr hr
  rw [he]
  exact mkQ_mem_level R d n w (fun b hb => lt_of_lt_of_le (hw b hb) (Nat.le_of_lt_succ ha))

/-- The support decrease on generators extends to all classes in the generated level. -/
theorem level_difference (d : C → ℕ)
    (hdrop : ∀ l a, ∃ w : C →₀ ℤ,
      (∀ b ∈ w.support, d b < d a) ∧
      Finsupp.single (σ l a) 1 - Finsupp.single a 1 - w ∈ R)
    (n : ℕ) (l : T) (b : PresentedGroup R) (hb : b ∈ level R d (n + 1)) :
    quotientAction R σ hR l b - b ∈ level R d n := by
  let δ : PresentedGroup R →ₗ[ℤ] PresentedGroup R := (quotientAction R σ hR l).toLinearMap - LinearMap.id
  change δ b ∈ level R d n
  apply (Submodule.span_le (p := (level R d n).comap δ)).mpr ?_ hb
  rintro b ⟨a, ha, rfl⟩
  exact generator_difference R σ hR d hdrop n l a ha

variable (e : C → ℚ) (he : ∀ v ∈ R, Finsupp.linearCombination ℤ e v = 0)

def euler : PresentedGroup R →ₗ[ℤ] ℚ :=
  R.liftQ (Finsupp.linearCombination ℤ e) he

@[simp] theorem euler_mkQ (v : C →₀ ℤ) :
    euler R e he (R.mkQ v) = Finsupp.linearCombination ℤ e v := rfl

@[simp] theorem euler_generator (a : C) : euler R e he (generator R a) = e a := by
  rw [generator, euler_mkQ]
  simp

theorem euler_action (l : T) (b : PresentedGroup R) (h : ∀ a, e (σ l a) = e a) :
    euler R e he (quotientAction R σ hR l b) = euler R e he b := by
  obtain ⟨v, rfl⟩ := R.mkQ_surjective b
  simp only [quotientAction_mkQ, euler_mkQ]
  have heq : (Finsupp.linearCombination ℤ e).comp (freeAction σ l).toLinearMap =
      Finsupp.linearCombination ℤ e := by
    apply Finsupp.lhom_ext
    intro a n
    simp [h]
  exact LinearMap.congr_fun heq v

end PhilipponMultiplicity.CoherentPresentation
end

end


section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators Topology
noncomputable section
universe u
namespace PhilipponMultiplicity

theorem filtered_twists_of_coherent_presentation
    (K : Type u) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (G : EmbeddedGroupProduct K)
    (τ : G.Point → (groupProjectiveClosure G ≃ groupProjectiveClosure G))
    (hzero : τ 0 = Equiv.refl _)
    (hadd : ∀ g h, τ (g+h) = (τ h).trans (τ g))
    (hregular : ∀ g, G.ambient.IsRegularAlong G.ambient
      (fun x : groupProjectiveClosure G => x.val) (fun x => (τ g x).val))
    (hgeometry : ∃ (L : Type u) (_ : AddCommGroup L) (_ : Module ℤ L)
      (A : Type) (_ : AddCommGroup A) (_ : Module ℤ A) (_ : Module.Finite ℤ A)
      (q : L →ₗ[ℤ] A), Function.Surjective q ∧
      ∃ (ρ : Multiplicative G.Point →* (L ≃ₗ[ℤ] L)) (c : G.FactorIndex → L),
        (∀ g x, q x = 0 → q (ρ g x) = 0) ∧
        ∃ (C : Type u) (σ : Multiplicative L →* Equiv.Perm C)
          (d : C → ℕ) (R : Submodule ℤ (C →₀ ℤ)) (e : C → ℚ),
          (∀ l v, v ∈ R → Finsupp.lmapDomain ℤ ℤ (σ l) v ∈ R) ∧
          (∀ v ∈ R, Finsupp.linearCombination ℤ e v = 0) ∧
          (∀ l a, ∃ w : C →₀ ℤ,
            (∀ b ∈ w.support, d b < d a) ∧
            Finsupp.single (σ (Multiplicative.ofAdd l) a) 1 -
              Finsupp.single a 1 - w ∈ R) ∧
          (∀ l, q l = 0 → ∀ a, e (σ (Multiplicative.ofAdd l) a) = e a) ∧
          ∀ (V : Set (groupProjectiveClosure G)),
            @IsClosed _ (TopologicalSpace.induced Subtype.val G.ambient.zariskiTopology) V →
            ∃ a : C,
              d a ≤ SectionThree.locusDimension G.ambient (Subtype.val '' V) ∧
              ∀ (g : G.Point) (D : G.FactorIndex → ℕ), (∀ i, 1 ≤ D i) →
                ∃ N : ℕ, ∀ n ≥ N,
                  e (σ (Multiplicative.ofAdd
                    (n • ρ (Multiplicative.ofAdd (-g)) (∑ i, (D i : ℤ) • c i))) a) =
                    (Hilbert.hilbertFunction K G.ambient.factorCount G.ambient.ambientDimension
                      (G.ambient.vanishingIdeal (Subtype.val '' (τ g '' V)))
                      (fun i => D i * n) : ℚ)) :
    ∃ (L : Type u) (_ : AddCommGroup L) (_ : Module ℤ L)
      (A : Type) (_ : AddCommGroup A) (_ : Module ℤ A) (_ : Module.Finite ℤ A)
      (q : L →ₗ[ℤ] A), Function.Surjective q ∧
      ∃ (ρ : Multiplicative G.Point →* (L ≃ₗ[ℤ] L)) (c : G.FactorIndex → L),
        (∀ g x, q x = 0 → q (ρ g x) = 0) ∧
        ∃ (B : Type u) (_ : AddCommGroup B) (_ : Module ℤ B)
          (β : Multiplicative L →* (B ≃ₗ[ℤ] B)) (χ : B →ₗ[ℤ] ℚ)
          (F : ℕ → Submodule ℤ B),
          F 0 = ⊥ ∧
          (∀ n y b, b ∈ F (n + 1) → β (Multiplicative.ofAdd y) b - b ∈ F n) ∧
          (∀ l, q l = 0 → ∀ b, χ (β (Multiplicative.ofAdd l) b) = χ b) ∧
          ∀ (V : Set (groupProjectiveClosure G)),
            @IsClosed _ (TopologicalSpace.induced Subtype.val G.ambient.zariskiTopology) V →
            ∃ b : B,
              b ∈ F (SectionThree.locusDimension G.ambient (Subtype.val '' V) + 1) ∧
              ∀ (g : G.Point) (D : G.FactorIndex → ℕ), (∀ i, 1 ≤ D i) →
                ∃ N : ℕ, ∀ n ≥ N,
                  χ (β (Multiplicative.ofAdd
                    (n • ρ (Multiplicative.ofAdd (-g)) (∑ i, (D i : ℤ) • c i))) b) =
                    (Hilbert.hilbertFunction K G.ambient.factorCount G.ambient.ambientDimension
                      (G.ambient.vanishingIdeal (Subtype.val '' (τ g '' V)))
                      (fun i => D i * n) : ℚ) := by
  classical
  obtain ⟨L, hL, hML, A, hA, hMA, hFA, q, hq, ρ, c, hker,
    C, σ, d, R, e, hR, he, hdrop, hEuler, hV⟩ := hgeometry
  let B := CoherentPresentation.PresentedGroup R
  let β := CoherentPresentation.quotientAction R σ hR
  let χ := CoherentPresentation.euler R e he
  let F := CoherentPresentation.level R d
  refine ⟨L, hL, hML, A, hA, hMA, hFA, q, hq, ρ, c, hker,
    B, inferInstance, inferInstance, β, χ, F,
    CoherentPresentation.level_zero R d, ?_, ?_, ?_⟩
  · intro n l b hb
    exact CoherentPresentation.level_difference R σ hR d
      (fun t a => hdrop t.toAdd a) n (Multiplicative.ofAdd l) b hb
  · intro l hl b
    exact CoherentPresentation.euler_action R σ hR e he
      (Multiplicative.ofAdd l) b (hEuler l hl)
  · intro V hclosed
    obtain ⟨a, ha, hrep⟩ := hV V hclosed
    refine ⟨CoherentPresentation.generator R a,
      CoherentPresentation.generator_mem_level R d _ a (Nat.lt_succ_of_le ha), ?_⟩
    intro g D hD
    obtain ⟨N, hN⟩ := hrep g D hD
    refine ⟨N, ?_⟩
    intro n hn
    exact (congrArg (CoherentPresentation.euler R e he)
      (CoherentPresentation.quotientAction_generator R σ hR
        (Multiplicative.ofAdd (n • ρ (Multiplicative.ofAdd (-g))
          (∑ i, (D i : ℤ) • c i))) a)).trans
      ((CoherentPresentation.euler_generator R e he _).trans (hN n hn))

end PhilipponMultiplicity
end

end

set_option autoImplicit false
open PhilipponMultiplicity
open scoped BigOperators Topology
universe u

theorem solution
    (K : Type u) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (G : EmbeddedGroupProduct K)
    (τ : G.Point → (groupProjectiveClosure G ≃ groupProjectiveClosure G))
    (hzero : τ 0 = Equiv.refl _)
    (hadd : ∀ g h, τ (g+h) = (τ h).trans (τ g))
    (hregular : ∀ g, G.ambient.IsRegularAlong G.ambient
      (fun x : groupProjectiveClosure G => x.val) (fun x => (τ g x).val)) :
    ∃ (L : Type u) (_ : AddCommGroup L) (_ : Module ℤ L)
      (A : Type) (_ : AddCommGroup A) (_ : Module ℤ A) (_ : Module.Finite ℤ A)
      (q : L →ₗ[ℤ] A), Function.Surjective q ∧
      ∃ (ρ : Multiplicative G.Point →* (L ≃ₗ[ℤ] L)) (c : G.FactorIndex → L),
        (∀ g x, q x = 0 → q (ρ g x) = 0) ∧
        ∃ (B : Type u) (_ : AddCommGroup B) (_ : Module ℤ B)
          (β : Multiplicative L →* (B ≃ₗ[ℤ] B)) (χ : B →ₗ[ℤ] ℚ)
          (F : ℕ → Submodule ℤ B),
          F 0 = ⊥ ∧
          (∀ n y b, b ∈ F (n + 1) → β (Multiplicative.ofAdd y) b - b ∈ F n) ∧
          (∀ l, q l = 0 → ∀ b, χ (β (Multiplicative.ofAdd l) b) = χ b) ∧
          ∀ (V : Set (groupProjectiveClosure G)),
            @IsClosed _ (TopologicalSpace.induced Subtype.val G.ambient.zariskiTopology) V →
            ∃ b : B,
              b ∈ F (SectionThree.locusDimension G.ambient (Subtype.val '' V) + 1) ∧
              ∀ (g : G.Point) (D : G.FactorIndex → ℕ), (∀ i, 1 ≤ D i) →
                ∃ N : ℕ, ∀ n ≥ N,
                  χ (β (Multiplicative.ofAdd
                    (n • ρ (Multiplicative.ofAdd (-g)) (∑ i, (D i : ℤ) • c i))) b) =
                    (Hilbert.hilbertFunction K G.ambient.factorCount G.ambient.ambientDimension
                      (G.ambient.vanishingIdeal (Subtype.val '' (τ g '' V)))
                      (fun i => D i * n) : ℚ) := by
  exact filtered_twists_of_coherent_presentation K hK G τ hzero hadd hregular
    (closure_action_has_coherent_generator_presentation K hK G τ hzero hadd hregular)
