-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P11.abstract_product
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T13:09:46.204917+00:00
-- url     : https://prove2.me/submissions/9c151c6a-362d-4b64-b485-3500fa3a5e92

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

open X6P11 in
theorem solution {F : Type*} [CommRing F] [Algebra ℂ F]
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
    [CompleteSpace X] (C : ElementaryCalculus F X) (hC : IsProper C)
    (f g q e1 e2 e3 : F)
    (hf : Regularisable C f) (hg : Regularisable C g)
    (hq : RegularInverse C f q)
    (he1 : Regularisable C e1 ∧ e1 ∈ boundedElements (calculusValue C))
    (he2 : Regularisable C e2 ∧ e2 ∈ boundedElements (calculusValue C))
    (he3 : Regularisable C e3 ∧ e3 ∈ boundedElements (calculusValue C))
    (hi1 : ∃ r, RegularInverse C e1 r) (hi2 : ∃ r, RegularInverse C e2 r)
    (hi3 : ∃ r, RegularInverse C e3 r)
    (h1 : Regularisable C (e1 * f) ∧ (e1 * f) ∈ boundedElements (calculusValue C))
    (h2 : Regularisable C (e2 * g) ∧ (e2 * g) ∈ boundedElements (calculusValue C))
    (h3 : Regularisable C (e3 * q) ∧ (e3 * q) ∈ boundedElements (calculusValue C))
    (p : Polynomial ℂ) (hp : p.eval 0 ≠ 0)
    (hrange : graphRange (calculusValue C (Polynomial.aeval e3 p)) ⊆
      graphRange (calculusValue C (e1 * e2))) :
    graphMul (calculusValue C f) (calculusValue C g) = calculusValue C (f * g) := by
  have hfg : Regularisable C (f * g) := Reg_mul C hf hg
  ext ⟨x, z⟩
  constructor
  · rintro ⟨y, hy, hz⟩
    exact mul_rule C hf hg hy hz
  intro hxz
  -- key: dom Φ(fg) ⊆ dom Φ(g)
  have t3 := total_of_bounded C he3.2
  have t3q := total_of_bounded C h3.2
  have t1 := total_of_bounded C he1.2
  have t2g := total_of_bounded C h2.2
  -- decomposition p = c0 + X * r
  set c0 := p.eval 0
  obtain ⟨r, hr⟩ : ∃ r : Polynomial ℂ, p = Polynomial.C c0 + Polynomial.X * r := by
    have : Polynomial.X ∣ p - Polynomial.C c0 := by
      rw [Polynomial.X_dvd_iff, Polynomial.coeff_sub, Polynomial.coeff_C_zero,
        Polynomial.coeff_zero_eq_eval_zero, sub_self]
    obtain ⟨r, hr⟩ := this
    exact ⟨r, by rw [← hr]; ring⟩
  obtain ⟨rr, rt⟩ := poly C hC he3.1 t3 r
  set R := Polynomial.aeval e3 r
  have hpe : Polynomial.aeval e3 p = c0 • (1 : F) + e3 * R := by
    rw [hr, map_add, map_mul, Polynomial.aeval_C, Polynomial.aeval_X,
      Algebra.algebraMap_eq_smul_one]
  -- dom Φ(g) membership helper
  have domg_of : ∀ w : X, (∃ u, (u, w) ∈ calculusValue C (e1 * e2)) →
      ∃ v, (w, v) ∈ calculusValue C g := by
    rintro w ⟨u, hu⟩
    have rge : Regularisable C (e1 * (e2 * g)) := Reg_mul C he1.1 h2.1
    obtain ⟨v, hv⟩ := total_mul C he1.1 h2.1 t1 t2g u
    have : e1 * (e2 * g) = g * (e1 * e2) := by ring
    rw [this] at hv
    exact ⟨v, mul_dom C hg (Reg_mul C he1.1 he2.1) hu hv⟩
  -- y := Φ(R) x lies in dom Φ(fg)
  obtain ⟨y, hy⟩ := rt x
  obtain ⟨y2, hy2⟩ : ∃ y2, (y, y2) ∈ calculusValue C (f * g) := by
    obtain ⟨w, hw⟩ := rt z
    have h1' := mul_rule C rr hfg hxz hw
    rw [mul_comm] at h1'
    exact ⟨w, mul_dom C hfg rr hy h1'⟩
  -- Φ(e3) y ∈ dom Φ(g)
  obtain ⟨s, hs⟩ := t3 y
  have hge3 : ∃ v, (s, v) ∈ calculusValue C g := by
    obtain ⟨w, hw⟩ := t3q y2
    have hm := mul_rule C h3.1 hfg hy2 hw
    have : e3 * q * (f * g) = g * e3 := by
      have hfq := hq.1
      calc e3 * q * (f * g) = e3 * g * (f * q) := by ring
        _ = g * e3 := by rw [hfq]; ring
    rw [this] at hm
    exact ⟨w, mul_dom C hg he3.1 hs hm⟩
  -- Φ(p(e3)) x = c0 x + s
  have hpx : (x, c0 • x + s) ∈ calculusValue C (Polynomial.aeval e3 p) := by
    rw [hpe]
    have r1 : Regularisable C (1 : F) := hC
    exact add_rule C (Reg_smul C c0 r1) (Reg_mul C he3.1 rr)
      (smul_rule C c0 r1 (one_rule C hC x)) (mul_rule C he3.1 rr hy hs)
  obtain ⟨u, hu⟩ := hrange ⟨x, hpx⟩
  obtain ⟨v1, hv1⟩ := domg_of _ ⟨u, hu⟩
  obtain ⟨v2, hv2⟩ := hge3
  have hxg : (x, c0⁻¹ • (v1 + (-1 : ℂ) • v2)) ∈ calculusValue C g := by
    have := lin_smul C c0⁻¹ hg (lin_add C hg hv1 (lin_smul C (-1) hg hv2))
    convert this using 2
    rw [neg_one_smul, add_neg_cancel_right, smul_smul, inv_mul_cancel₀ hp, one_smul]
  exact ⟨_, hxg, mul_dom C hf hg hxg hxz⟩
