-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P11.quotient_calculus
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T13:13:06.613326+00:00
-- url     : https://prove2.me/submissions/556202c3-5ceb-4baa-b1ef-ffd58acd3c72

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P11

noncomputable section

attribute [local instance] Classical.propDecidable

open Set Filter MeasureTheory
open QAlgorithms.Papers.Independent.Next46.P06
open QAlgorithms.Papers.Independent.Renew46.P11

namespace X6P11

variable {F : Type*} [CommRing F] [Algebra ℂ F]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

section
variable (C : ElementaryCalculus F X)

lemma E_add {a b : F} (ha : a ∈ C.elementary) (hb : b ∈ C.elementary) :
    a + b ∈ C.elementary := (C.representation.1.2.1 a ha b hb).1
lemma E_mul {a b : F} (ha : a ∈ C.elementary) (hb : b ∈ C.elementary) :
    a * b ∈ C.elementary := (C.representation.1.2.1 a ha b hb).2
lemma E_smul (c : ℂ) {a : F} (ha : a ∈ C.elementary) : c • a ∈ C.elementary :=
  C.representation.1.2.2 c a ha
lemma rho_add {a b : F} (ha : a ∈ C.elementary) (hb : b ∈ C.elementary) :
    C.rho (a + b) = C.rho a + C.rho b := (C.representation.2.2.1 a ha b hb).1
lemma rho_mul {a b : F} (ha : a ∈ C.elementary) (hb : b ∈ C.elementary) (x : X) :
    C.rho (a * b) x = C.rho a (C.rho b x) := by
  rw [(C.representation.2.2.1 a ha b hb).2]; rfl
lemma rho_smul (c : ℂ) {a : F} (ha : a ∈ C.elementary) : C.rho (c • a) = c • C.rho a :=
  C.representation.2.2.2 c a ha

/-- regulariser independence -/
lemma indep {f e e' : F} (he : IsRegularizer C f e) (he' : IsRegularizer C f e') {x y : X}
    (h : C.rho (e * f) x = C.rho e y) : C.rho (e' * f) x = C.rho e' y := by
  obtain ⟨h1, h2, h3⟩ := he
  obtain ⟨h1', h2', h3'⟩ := he'
  apply h3
  calc C.rho e (C.rho (e' * f) x) = C.rho (e * (e' * f)) x := (rho_mul C h1 h2' x).symm
    _ = C.rho (e' * (e * f)) x := by congr 2; ring
    _ = C.rho e' (C.rho (e * f) x) := rho_mul C h1' h2 x
    _ = C.rho e' (C.rho e y) := by rw [h]
    _ = C.rho (e' * e) y := (rho_mul C h1' h1 y).symm
    _ = C.rho (e * e') y := by rw [mul_comm]
    _ = C.rho e (C.rho e' y) := rho_mul C h1 h1' y

lemma mem_cv {f e : F} (he : IsRegularizer C f e) (x y : X) :
    (x, y) ∈ calculusValue C f ↔ C.rho (e * f) x = C.rho e y := by
  have hr : Regularisable C f := ⟨e, he⟩
  simp only [calculusValue, dif_pos hr, Set.mem_setOf_eq]
  exact ⟨fun h => indep C (Classical.choose_spec hr) he h,
    fun h => indep C he (Classical.choose_spec hr) h⟩

lemma reg_mul {a b e e' : F} (he : IsRegularizer C a e) (he' : IsRegularizer C b e') :
    IsRegularizer C (a * b) (e * e') := by
  obtain ⟨h1, h2, h3⟩ := he
  obtain ⟨h1', h2', h3'⟩ := he'
  refine ⟨E_mul C h1 h1', ?_, ?_⟩
  · have : e * e' * (a * b) = (e * a) * (e' * b) := by ring
    rw [this]; exact E_mul C h2 h2'
  · intro x y hxy
    rw [(C.representation.2.2.1 e h1 e' h1').2] at hxy
    exact h3' (h3 hxy)

lemma reg_add {a b e e' : F} (he : IsRegularizer C a e) (he' : IsRegularizer C b e') :
    IsRegularizer C (a + b) (e * e') := by
  obtain ⟨h1, h2, h3⟩ := he
  obtain ⟨h1', h2', h3'⟩ := he'
  refine ⟨E_mul C h1 h1', ?_, (reg_mul C ⟨h1, h2, h3⟩ ⟨h1', h2', h3'⟩).2.2⟩
  have : e * e' * (a + b) = e' * (e * a) + e * (e' * b) := by ring
  rw [this]; exact E_add C (E_mul C h1' h2) (E_mul C h1 h2')

lemma reg_smul (c : ℂ) {a e : F} (he : IsRegularizer C a e) : IsRegularizer C (c • a) e := by
  obtain ⟨h1, h2, h3⟩ := he
  refine ⟨h1, ?_, h3⟩
  rw [mul_smul_comm]; exact E_smul C c h2

lemma Reg_mul {a b : F} (ha : Regularisable C a) (hb : Regularisable C b) :
    Regularisable C (a * b) := ⟨_, reg_mul C ha.choose_spec hb.choose_spec⟩
lemma Reg_add {a b : F} (ha : Regularisable C a) (hb : Regularisable C b) :
    Regularisable C (a + b) := ⟨_, reg_add C ha.choose_spec hb.choose_spec⟩
lemma Reg_smul (c : ℂ) {a : F} (ha : Regularisable C a) : Regularisable C (c • a) :=
  ⟨_, reg_smul C c ha.choose_spec⟩

/-- product rule (forward inclusion) -/
lemma mul_rule {a b : F} (ha : Regularisable C a) (hb : Regularisable C b) {x y z : X}
    (hxy : (x, y) ∈ calculusValue C b) (hyz : (y, z) ∈ calculusValue C a) :
    (x, z) ∈ calculusValue C (a * b) := by
  obtain ⟨e, he⟩ := ha
  obtain ⟨e', he'⟩ := hb
  rw [mem_cv C he'] at hxy
  rw [mem_cv C he] at hyz
  rw [mem_cv C (reg_mul C he he')]
  obtain ⟨h1, h2, h3⟩ := he
  obtain ⟨h1', h2', h3'⟩ := he'
  calc C.rho (e * e' * (a * b)) x = C.rho ((e * a) * (e' * b)) x := by congr 2; ring
    _ = C.rho (e * a) (C.rho (e' * b) x) := rho_mul C h2 h2' x
    _ = C.rho (e * a) (C.rho e' y) := by rw [hxy]
    _ = C.rho (e' * (e * a)) y := by rw [← rho_mul C h2 h1', mul_comm]
    _ = C.rho e' (C.rho e z) := by rw [rho_mul C h1' h2, hyz]
    _ = C.rho (e * e') z := by rw [← rho_mul C h1' h1, mul_comm]

/-- product rule (domain part) -/
lemma mul_dom {a b : F} (ha : Regularisable C a) (hb : Regularisable C b) {x y z : X}
    (hxy : (x, y) ∈ calculusValue C b) (hxz : (x, z) ∈ calculusValue C (a * b)) :
    (y, z) ∈ calculusValue C a := by
  obtain ⟨e, he⟩ := ha
  obtain ⟨e', he'⟩ := hb
  rw [mem_cv C he'] at hxy
  rw [mem_cv C he]
  rw [mem_cv C (reg_mul C he he')] at hxz
  obtain ⟨h1, h2, h3⟩ := he
  obtain ⟨h1', h2', h3'⟩ := he'
  apply h3'
  calc C.rho e' (C.rho (e * a) y) = C.rho (e * a) (C.rho e' y) := by
        rw [← rho_mul C h1' h2, ← rho_mul C h2 h1', mul_comm]
    _ = C.rho (e * a) (C.rho (e' * b) x) := by rw [hxy]
    _ = C.rho (e * e' * (a * b)) x := by rw [← rho_mul C h2 h2']; congr 2; ring
    _ = C.rho (e * e') z := hxz
    _ = C.rho e' (C.rho e z) := by rw [mul_comm, rho_mul C h1' h1]

lemma add_rule {a b : F} (ha : Regularisable C a) (hb : Regularisable C b) {x y z : X}
    (hy : (x, y) ∈ calculusValue C a) (hz : (x, z) ∈ calculusValue C b) :
    (x, y + z) ∈ calculusValue C (a + b) := by
  obtain ⟨e, he⟩ := ha
  obtain ⟨e', he'⟩ := hb
  rw [mem_cv C he] at hy
  rw [mem_cv C he'] at hz
  rw [mem_cv C (reg_add C he he')]
  obtain ⟨h1, h2, h3⟩ := he
  obtain ⟨h1', h2', h3'⟩ := he'
  have e1 : e * e' * (a + b) = e' * (e * a) + e * (e' * b) := by ring
  rw [e1, rho_add C (E_mul C h1' h2) (E_mul C h1 h2'), ContinuousLinearMap.add_apply,
    rho_mul C h1' h2, rho_mul C h1 h2', hy, hz, map_add]
  rw [← rho_mul C h1' h1, ← rho_mul C h1 h1', mul_comm e' e]

lemma smul_rule (c : ℂ) {a : F} (ha : Regularisable C a) {x y : X}
    (hy : (x, y) ∈ calculusValue C a) : (x, c • y) ∈ calculusValue C (c • a) := by
  obtain ⟨e, he⟩ := ha
  rw [mem_cv C he] at hy
  rw [mem_cv C (reg_smul C c he), mul_smul_comm, rho_smul C c he.2.1,
    ContinuousLinearMap.smul_apply, hy, map_smul]

lemma func {a : F} (ha : Regularisable C a) {x y y' : X}
    (hy : (x, y) ∈ calculusValue C a) (hy' : (x, y') ∈ calculusValue C a) : y = y' := by
  obtain ⟨e, he⟩ := ha
  rw [mem_cv C he] at hy hy'
  exact he.2.2 (hy.symm.trans hy')

lemma lin_add {a : F} (ha : Regularisable C a) {x y x' y' : X}
    (h : (x, y) ∈ calculusValue C a) (h' : (x', y') ∈ calculusValue C a) :
    (x + x', y + y') ∈ calculusValue C a := by
  obtain ⟨e, he⟩ := ha
  rw [mem_cv C he] at h h' ⊢
  simp [map_add, h, h']

lemma lin_smul (c : ℂ) {a : F} (ha : Regularisable C a) {x y : X}
    (h : (x, y) ∈ calculusValue C a) : (c • x, c • y) ∈ calculusValue C a := by
  obtain ⟨e, he⟩ := ha
  rw [mem_cv C he] at h ⊢
  simp [map_smul, h]

def Total (a : F) : Prop := ∀ x : X, ∃ y, (x, y) ∈ calculusValue C a

lemma total_of_bounded {a : F} (h : a ∈ boundedElements (calculusValue C)) : Total C a := by
  obtain ⟨T, hT⟩ := h
  intro x; exact ⟨T x, by rw [hT]; rfl⟩

lemma total_mul {a b : F} (ha : Regularisable C a) (hb : Regularisable C b)
    (ta : Total C a) (tb : Total C b) : Total C (a * b) := by
  intro x
  obtain ⟨y, hy⟩ := tb x
  obtain ⟨z, hz⟩ := ta y
  exact ⟨z, mul_rule C ha hb hy hz⟩

lemma total_add {a b : F} (ha : Regularisable C a) (hb : Regularisable C b)
    (ta : Total C a) (tb : Total C b) : Total C (a + b) := by
  intro x
  obtain ⟨y, hy⟩ := ta x
  obtain ⟨z, hz⟩ := tb x
  exact ⟨y + z, add_rule C ha hb hy hz⟩

lemma total_smul (c : ℂ) {a : F} (ha : Regularisable C a) (ta : Total C a) :
    Total C (c • a) := by
  intro x
  obtain ⟨y, hy⟩ := ta x
  exact ⟨c • y, smul_rule C c ha hy⟩

lemma one_rule (hC : IsProper C) (x : X) : (x, x) ∈ calculusValue C 1 := by
  obtain ⟨e, he⟩ := hC
  rw [mem_cv C he, mul_one]

lemma poly (hC : IsProper C) {b : F} (hb : Regularisable C b) (tb : Total C b) (P : Polynomial ℂ) :
    Regularisable C (Polynomial.aeval b P) ∧ Total C (Polynomial.aeval b P) := by
  have r1 : Regularisable C (1 : F) := hC
  have t1 : Total C (1 : F) := fun x => ⟨x, one_rule C hC x⟩
  induction P using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add]; exact ⟨Reg_add C hp.1 hq.1, total_add C hp.1 hq.1 hp.2 hq.2⟩
  | monomial n c =>
    rw [Polynomial.aeval_monomial, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
    have : Regularisable C (b ^ n) ∧ Total C (b ^ n) := by
      induction n with
      | zero => simpa using ⟨r1, t1⟩
      | succ k ih =>
        rw [pow_succ]; exact ⟨Reg_mul C ih.1 hb, total_mul C ih.1 hb ih.2 tb⟩
    exact ⟨Reg_smul C c this.1, total_smul C c this.1 this.2⟩

end

end X6P11

open QAlgorithms.Papers.Independent.Claimed50.P05 (graphDomain) in
open X6P11 in
theorem solution {F : Type*} [CommRing F] [Algebra ℂ F]
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℂ Y] [CompleteSpace Y]
    [CompleteSpace X] [CompleteSpace Y] (C : ElementaryCalculus F X) (D : ElementaryCalculus F Y)
    (hC : IsProper C) (hD : IsProper D) (hE : D.elementary = C.elementary)
    (u : X →L[ℂ] Y) (hu : Function.Surjective u)
    (hint : ∀ g ∈ C.elementary, (D.rho g).comp u = u.comp (C.rho g))
    (f e : F) (he : IsRegularizer C f e)
    (hker : (C.rho e) '' (u.ker : Set X) = (u.ker : Set X)) :
    IsRegularizer D f e ∧
    graphPrecompose (calculusValue D f) u = graphPostcompose u (calculusValue C f) ∧
    graphDomain (calculusValue D f) = u '' graphDomain (calculusValue C f) := by
  obtain ⟨h1, h2, h3⟩ := he
  have hi : ∀ g ∈ C.elementary, ∀ x, D.rho g (u x) = u (C.rho g x) := fun g hg x => by
    have := congrArg (fun T : X →L[ℂ] Y => T x) (hint g hg); simpa using this
  -- kernel lifting
  have lift : ∀ x : X, u x = 0 → ∃ k, u k = 0 ∧ C.rho e k = x := by
    intro x hx
    have : x ∈ (C.rho e) '' (u.ker : Set X) := by rw [hker]; exact hx
    obtain ⟨k, hk, hkx⟩ := this
    exact ⟨k, hk, hkx⟩
  have hD' : IsRegularizer D f e := by
    refine ⟨hE ▸ h1, hE ▸ h2, ?_⟩
    rw [injective_iff_map_eq_zero]
    intro y hy
    obtain ⟨x, rfl⟩ := hu y
    rw [hi e h1] at hy
    obtain ⟨k, hk, hkx⟩ := lift _ hy
    have : k = x := h3 hkx
    rw [← this, hk]
  have hpre : graphPrecompose (calculusValue D f) u = graphPostcompose u (calculusValue C f) := by
    ext ⟨x, y⟩
    simp only [graphPrecompose, graphPostcompose, Set.mem_setOf_eq]
    rw [mem_cv D hD']
    constructor
    · intro h
      obtain ⟨y0, rfl⟩ := hu y
      rw [hi _ h2, hi _ h1] at h
      have h0 : u (C.rho (e * f) x - C.rho e y0) = 0 := by rw [map_sub, h, sub_self]
      obtain ⟨k, hk, hkx⟩ := lift _ h0
      refine ⟨y0 + k, ?_, by rw [map_add, hk, add_zero]⟩
      rw [mem_cv C ⟨h1, h2, h3⟩, map_add, hkx]; abel
    · rintro ⟨y', hy', rfl⟩
      rw [mem_cv C ⟨h1, h2, h3⟩] at hy'
      rw [hi _ h2, hi _ h1, hy']
  refine ⟨hD', hpre, ?_⟩
  ext y
  constructor
  · rintro ⟨z, hz⟩
    obtain ⟨x, rfl⟩ := hu y
    have : (x, z) ∈ graphPrecompose (calculusValue D f) u := hz
    rw [hpre] at this
    obtain ⟨y', hy', -⟩ := this
    exact ⟨x, ⟨y', hy'⟩, rfl⟩
  · rintro ⟨x, ⟨y', hy'⟩, rfl⟩
    have : (x, u y') ∈ graphPostcompose u (calculusValue C f) := ⟨y', hy', rfl⟩
    rw [← hpre] at this
    exact ⟨u y', this⟩
