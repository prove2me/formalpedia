-- Prove2me | solution 1 for ThompsonAmenability.not_isAmenable_F
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-07T08:31:37.581782+00:00
-- url     : https://prove2.me/submissions/d5a1038f-7d1a-4e0a-9b21-4a713d97614d

import Definitions.Def_Garrido_Amenability
import Definitions.Def_CannonFloydParry
import Theorems.Thm_Garrido_isAmenable_subgroup
import Theorems.Thm_Garrido_isAmenable_tfae
import Mathlib

universe uG uα uE uι uβ uX uH

section
section
namespace OAI

noncomputable section

open scoped ENNReal


namespace ThompsonNonamenability

abbrev UnitInterval := Set.Icc (0 : ℝ) 1

def unitIntervalZero : UnitInterval := ⟨0, le_rfl, zero_le_one⟩
def unitIntervalOne : UnitInterval := ⟨1, zero_le_one, le_rfl⟩

structure IntervalHomeomorph where
  toHomeomorph : UnitInterval ≃ₜ UnitInterval

namespace IntervalHomeomorph

instance : CoeFun IntervalHomeomorph (fun _ => UnitInterval → UnitInterval) :=
  ⟨fun f => f.toHomeomorph⟩

end IntervalHomeomorph

def IsDyadic (x : ℝ) : Prop :=
  ∃ (k : ℤ) (n : ℕ), x = (k : ℝ) / (2 : ℝ) ^ n

structure DyadicPLWitness (f : IntervalHomeomorph) where
  pieceCount : ℕ
  positive : 0 < pieceCount
  knots : Fin (pieceCount + 1) → UnitInterval
  strictMono_knots : StrictMono knots
  first : knots 0 = unitIntervalZero
  last : knots (Fin.last pieceCount) = unitIntervalOne
  dyadic : ∀ i, IsDyadic (knots i : ℝ)
  cover : ∀ x : UnitInterval, ∃ i : Fin pieceCount,
    knots i.castSucc ≤ x ∧ x ≤ knots i.succ
  exponent : Fin pieceCount → ℤ
  affine : ∀ (i : Fin pieceCount) (x : UnitInterval),
    knots i.castSucc ≤ x → x ≤ knots i.succ →
    (f x : ℝ) = (f (knots i.castSucc) : ℝ) +
      (2 : ℝ) ^ exponent i * ((x : ℝ) - (knots i.castSucc : ℝ))

def HasDyadicPLPieces (f : IntervalHomeomorph) : Prop := Nonempty (DyadicPLWitness f)

def F := {f : IntervalHomeomorph // StrictMono f ∧ HasDyadicPLPieces f}

abbrev BoundedReal (G : Type uG) := lp (fun _ : G => ℝ) ∞

variable {G : Type uG} [Group G]

def leftPull (h : G) : BoundedReal G →ₗ[ℝ] BoundedReal G where
  toFun f := ⟨fun g => f (h * g), memℓp_infty ⟨‖f‖, by
    rintro y ⟨g, rfl⟩
    exact lp.norm_apply_le_norm ENNReal.top_ne_zero f (h * g)⟩⟩
  map_add' f g := by
    apply lp.ext
    funext x
    rfl
  map_smul' r f := by
    apply lp.ext
    funext x
    rfl

structure InvariantMean (G : Type uG) [Group G] where
  toLinearMap : BoundedReal G →ₗ[ℝ] ℝ
  positive : ∀ f : BoundedReal G, (∀ g, 0 ≤ f g) → 0 ≤ toLinearMap f
  normalized : toLinearMap 1 = 1
  left_invariant : ∀ (h : G) (f : BoundedReal G),
    toLinearMap (leftPull h f) = toLinearMap f

end ThompsonNonamenability

end

end OAI

end
end

section
section
namespace OAI

/-!
# Actual homeomorphisms of the real unit interval

The wrapper supplies the composition group explicitly. In particular, its
multiplication is function composition in the order `(h * g) x = h (g x)`.
Its carrier is equivalent to the actual interval homeomorphisms, without
quotients or an abstract group action.
-/

namespace ThompsonNonamenability

@[simp] theorem coe_unitIntervalZero : (unitIntervalZero : ℝ) = 0 := rfl
@[simp] theorem coe_unitIntervalOne : (unitIntervalOne : ℝ) = 1 := rfl

namespace IntervalHomeomorph

@[ext] theorem ext {f g : IntervalHomeomorph} (h : ∀ x, f x = g x) : f = g := by
  cases f with
  | mk f =>
    cases g with
    | mk g =>
      congr 1
      exact Homeomorph.ext h

def homeomorphEquiv : IntervalHomeomorph ≃ (UnitInterval ≃ₜ UnitInterval) where
  toFun := toHomeomorph
  invFun := IntervalHomeomorph.mk
  left_inv f := by cases f; rfl
  right_inv _ := rfl

@[simp] theorem homeomorphEquiv_apply (f : IntervalHomeomorph) :
    homeomorphEquiv f = f.toHomeomorph := rfl

instance : Group IntervalHomeomorph where
  one := ⟨Homeomorph.refl UnitInterval⟩
  mul f g := ⟨g.toHomeomorph.trans f.toHomeomorph⟩
  inv f := ⟨f.toHomeomorph.symm⟩
  mul_assoc _ _ _ := ext fun _ => rfl
  one_mul _ := ext fun _ => rfl
  mul_one _ := ext fun _ => rfl
  inv_mul_cancel f := ext f.toHomeomorph.symm_apply_apply

@[simp] theorem one_apply (x : UnitInterval) : (1 : IntervalHomeomorph) x = x := rfl

@[simp] theorem mul_apply (h g : IntervalHomeomorph) (x : UnitInterval) :
    (h * g) x = h (g x) := rfl

@[simp] theorem inv_apply_apply (f : IntervalHomeomorph) (x : UnitInterval) :
    f⁻¹ (f x) = x := f.toHomeomorph.symm_apply_apply x

@[simp] theorem apply_inv_apply (f : IntervalHomeomorph) (x : UnitInterval) :
    f (f⁻¹ x) = x := f.toHomeomorph.apply_symm_apply x

theorem strictMono_inv {f : IntervalHomeomorph} (hf : StrictMono f) :
    StrictMono (f⁻¹ : IntervalHomeomorph) := by
  intro x y hxy
  by_contra h
  have hyx : f⁻¹ y ≤ f⁻¹ x := le_of_not_gt h
  have h' := hf.monotone hyx
  simp only [apply_inv_apply] at h'
  exact (not_le_of_gt hxy) h'

theorem map_zero {f : IntervalHomeomorph} (hf : StrictMono f) :
    f unitIntervalZero = unitIntervalZero := by
  apply Subtype.ext
  apply le_antisymm
  have hx : unitIntervalZero ≤ f⁻¹ unitIntervalZero :=
    (f⁻¹ unitIntervalZero).property.1
  have h := hf.monotone hx
  simpa only [apply_inv_apply, Subtype.coe_le_coe] using h
  exact (f unitIntervalZero).property.1

theorem map_one {f : IntervalHomeomorph} (hf : StrictMono f) :
    f unitIntervalOne = unitIntervalOne := by
  apply Subtype.ext
  apply le_antisymm
  exact (f unitIntervalOne).property.2
  have hx : f⁻¹ unitIntervalOne ≤ unitIntervalOne :=
    (f⁻¹ unitIntervalOne).property.2
  have h := hf.monotone hx
  simpa only [apply_inv_apply, Subtype.coe_le_coe] using h

end IntervalHomeomorph

end ThompsonNonamenability

end OAI

end
end

section
section
namespace OAI

/-!
# Real dyadic arithmetic

Dyadic numbers are represented by an integer numerator and a nonnegative
power of two denominator. In particular, the grid denominator below is an
actual common denominator, not an assumption about the input finite set.
-/


namespace ThompsonNonamenability

theorem isDyadic_intCast (k : ℤ) : IsDyadic (k : ℝ) := by
  exact ⟨k, 0, by simp⟩

@[simp] theorem isDyadic_zero : IsDyadic (0 : ℝ) := by
  simpa using isDyadic_intCast 0

@[simp] theorem isDyadic_one : IsDyadic (1 : ℝ) := by
  simpa using isDyadic_intCast 1

theorem IsDyadic.neg {x : ℝ} (hx : IsDyadic x) : IsDyadic (-x) := by
  rcases hx with ⟨k, n, rfl⟩
  exact ⟨-k, n, by simp only [Int.cast_neg, neg_div]⟩

theorem IsDyadic.mul {x y : ℝ} (hx : IsDyadic x) (hy : IsDyadic y) :
    IsDyadic (x * y) := by
  rcases hx with ⟨k, n, rfl⟩
  rcases hy with ⟨l, m, rfl⟩
  refine ⟨k * l, n + m, ?_⟩
  simp only [Int.cast_mul, pow_add, div_mul_div_comm]

theorem IsDyadic.add {x y : ℝ} (hx : IsDyadic x) (hy : IsDyadic y) :
    IsDyadic (x + y) := by
  rcases hx with ⟨k, n, rfl⟩
  rcases hy with ⟨l, m, rfl⟩
  refine ⟨k * 2 ^ m + l * 2 ^ n, n + m, ?_⟩
  push_cast
  rw [pow_add]
  field_simp

theorem IsDyadic.sub {x y : ℝ} (hx : IsDyadic x) (hy : IsDyadic y) :
    IsDyadic (x - y) := by
  simpa only [sub_eq_add_neg] using hx.add hy.neg

theorem isDyadic_zpow (q : ℤ) : IsDyadic ((2 : ℝ) ^ q) := by
  cases q with
  | ofNat n =>
      simpa only [Int.ofNat_eq_natCast, zpow_natCast, Int.cast_pow, Int.cast_ofNat] using
        isDyadic_intCast ((2 : ℤ) ^ n)
  | negSucc n =>
      exact ⟨1, n + 1, by simp [zpow_negSucc, one_div]⟩

/-- Increasing a dyadic denominator does not change the represented number. -/
theorem dyadic_raise_denominator {x : ℝ} {n : ℕ}
    (hx : ∃ k : ℤ, x = (k : ℝ) / (2 : ℝ) ^ n) (m : ℕ) :
    ∃ k : ℤ, x = (k : ℝ) / (2 : ℝ) ^ (n + m) := by
  rcases hx with ⟨k, rfl⟩
  refine ⟨k * 2 ^ m, ?_⟩
  push_cast
  rw [pow_add]
  field_simp

theorem dyadic_denominator_mono {x : ℝ} {n N : ℕ}
    (hx : ∃ k : ℤ, x = (k : ℝ) / (2 : ℝ) ^ n) (hn : n ≤ N) :
    ∃ k : ℤ, x = (k : ℝ) / (2 : ℝ) ^ N := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  exact dyadic_raise_denominator hx m

/-- Every finite family of dyadic reals has a single power of two denominator. -/
theorem dyadic_common_denominator_finset {α : Type uα} (s : Finset α) (f : α → ℝ)
    (hs : ∀ a ∈ s, IsDyadic (f a)) :
    ∃ n : ℕ, ∀ a ∈ s, ∃ k : ℤ, f a = (k : ℝ) / (2 : ℝ) ^ n := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      exact ⟨0, by simp⟩
  | @insert a s ha ih =>
      obtain ⟨k, n, hn⟩ := hs a (Finset.mem_insert_self a s)
      obtain ⟨m, hm⟩ := ih (fun b hb => hs b (Finset.mem_insert_of_mem hb))
      refine ⟨n + m, ?_⟩
      intro b hb
      rcases Finset.mem_insert.mp hb with rfl | hb
      · exact dyadic_raise_denominator ⟨k, hn⟩ m
      · simpa only [Nat.add_comm m n] using dyadic_raise_denominator (hm b hb) n

/-- A dyadic representation in the unit interval has a natural grid index. -/
theorem dyadic_nat_numerator {x : ℝ} {k : ℤ} {n : ℕ}
    (hx : x = (k : ℝ) / (2 : ℝ) ^ n) (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    ∃ j : ℕ, j ≤ 2 ^ n ∧ x = (j : ℝ) / (2 : ℝ) ^ n := by
  have hden : (0 : ℝ) < (2 : ℝ) ^ n := pow_pos (by norm_num) n
  have hk0r : (0 : ℝ) ≤ (k : ℝ) := by
    have hh := (le_div_iff₀ hden).1 (hx ▸ h0)
    simpa only [zero_mul] using hh
  have hk0 : (0 : ℤ) ≤ k := by exact_mod_cast hk0r
  have hkr : (k : ℝ) ≤ (2 : ℝ) ^ n := (div_le_one hden).1 (hx ▸ h1)
  have hcast : (k.toNat : ℝ) = (k : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg hk0
  refine ⟨k.toNat, ?_, ?_⟩
  · have hj : (k.toNat : ℝ) ≤ (2 : ℝ) ^ n := by
      simpa only [hcast] using hkr
    exact_mod_cast hj
  · simpa only [hcast] using hx

end ThompsonNonamenability

end OAI

end
end

section
section
namespace OAI

/-!
# The ordinary finite-piece dyadic PL condition

A witness is a finite subdivision of the actual real interval, together with
an affine equality on each closed piece. Knots may be redundant. The witness
is existential in `HasDyadicPLPieces`, so its choice is not part of a group
element's identity.
-/

namespace ThompsonNonamenability

namespace DyadicPLWitness

theorem knot_le_next {f : IntervalHomeomorph} (w : DyadicPLWitness f)
    (i : Fin w.pieceCount) : w.knots i.castSucc ≤ w.knots i.succ :=
  (w.strictMono_knots (Fin.castSucc_lt_succ_iff.mpr le_rfl)).le

theorem image_knots_dyadic {f : IntervalHomeomorph} (w : DyadicPLWitness f)
    (hf : StrictMono f) (i : Fin (w.pieceCount + 1)) :
    IsDyadic (f (w.knots i) : ℝ) := by
  refine Fin.induction ?_ ?_ i
  · simpa only [w.first, IntervalHomeomorph.map_zero hf, coe_unitIntervalZero]
      using isDyadic_zero
  · intro j hj
    rw [w.affine j (w.knots j.succ) (w.knot_le_next j) le_rfl]
    exact hj.add ((isDyadic_zpow (w.exponent j)).mul
      ((w.dyadic j.succ).sub (w.dyadic j.castSucc)))

theorem map_dyadic {f : IntervalHomeomorph} (w : DyadicPLWitness f)
    (hf : StrictMono f) {x : UnitInterval} (hx : IsDyadic (x : ℝ)) :
    IsDyadic (f x : ℝ) := by
  obtain ⟨i, hleft, hright⟩ := w.cover x
  rw [w.affine i x hleft hright]
  exact (w.image_knots_dyadic hf i.castSucc).add
    ((isDyadic_zpow (w.exponent i)).mul (hx.sub (w.dyadic i.castSucc)))

def identity : DyadicPLWitness (1 : IntervalHomeomorph) where
  pieceCount := 1
  positive := Nat.zero_lt_succ 0
  knots := Fin.cases unitIntervalZero (fun _ => unitIntervalOne)
  strictMono_knots := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [unitIntervalZero, unitIntervalOne]
    change (0 : ℝ) < 1
    exact zero_lt_one
  first := rfl
  last := rfl
  dyadic := by
    intro i
    fin_cases i
    · exact isDyadic_zero
    · exact isDyadic_one
  cover := by
    intro x
    exact ⟨0, x.property⟩
  exponent := fun _ => 0
  affine := by
    intro i x hleft hright
    simp only [IntervalHomeomorph.one_apply, zpow_zero, one_mul]
    ring

def inverse {f : IntervalHomeomorph} (w : DyadicPLWitness f) (hf : StrictMono f) :
    DyadicPLWitness f⁻¹ where
  pieceCount := w.pieceCount
  positive := w.positive
  knots := fun i => f (w.knots i)
  strictMono_knots := hf.comp w.strictMono_knots
  first := by rw [w.first, IntervalHomeomorph.map_zero hf]
  last := by rw [w.last, IntervalHomeomorph.map_one hf]
  dyadic := w.image_knots_dyadic hf
  cover := by
    intro x
    obtain ⟨i, hleft, hright⟩ := w.cover (f⁻¹ x)
    refine ⟨i, ?_, ?_⟩
    · simpa only [IntervalHomeomorph.apply_inv_apply] using hf.monotone hleft
    · simpa only [IntervalHomeomorph.apply_inv_apply] using hf.monotone hright
  exponent := fun i => -w.exponent i
  affine := by
    intro i x hleft hright
    have hleft' : w.knots i.castSucc ≤ f⁻¹ x := by
      apply hf.le_iff_le.mp
      simpa only [IntervalHomeomorph.apply_inv_apply] using hleft
    have hright' : f⁻¹ x ≤ w.knots i.succ := by
      apply hf.le_iff_le.mp
      simpa only [IntervalHomeomorph.apply_inv_apply] using hright
    have h := w.affine i (f⁻¹ x) hleft' hright'
    simp only [IntervalHomeomorph.apply_inv_apply] at h
    simp only [IntervalHomeomorph.inv_apply_apply, zpow_neg]
    have hpow : (2 : ℝ) ^ w.exponent i ≠ 0 := zpow_ne_zero _ (by norm_num)
    rw [h]
    field_simp [hpow]
    ring

end DyadicPLWitness

theorem hasDyadicPLPieces_one : HasDyadicPLPieces (1 : IntervalHomeomorph) :=
  ⟨DyadicPLWitness.identity⟩

theorem HasDyadicPLPieces.inv {f : IntervalHomeomorph}
    (h : HasDyadicPLPieces f) (hf : StrictMono f) : HasDyadicPLPieces f⁻¹ := by
  obtain ⟨w⟩ := h
  exact ⟨w.inverse hf⟩

namespace F

def toIntervalHomeomorph (g : F) : IntervalHomeomorph := g.val

instance : CoeFun F (fun _ => UnitInterval → UnitInterval) :=
  ⟨fun g => g.toIntervalHomeomorph⟩

def toHomeomorph (g : F) : UnitInterval ≃ₜ UnitInterval :=
  g.toIntervalHomeomorph.toHomeomorph

theorem strictMono (g : F) : StrictMono g := g.property.1

theorem hasDyadicPLPieces (g : F) : HasDyadicPLPieces g.toIntervalHomeomorph :=
  g.property.2

noncomputable def witness (g : F) : DyadicPLWitness g.toIntervalHomeomorph :=
  Classical.choice g.hasDyadicPLPieces

@[simp] theorem map_zero (g : F) : g unitIntervalZero = unitIntervalZero :=
  IntervalHomeomorph.map_zero g.strictMono

@[simp] theorem map_one (g : F) : g unitIntervalOne = unitIntervalOne :=
  IntervalHomeomorph.map_one g.strictMono

@[ext] theorem ext {g h : F} (heq : ∀ x, g x = h x) : g = h := by
  apply Subtype.ext
  exact IntervalHomeomorph.ext heq

end F

end ThompsonNonamenability

end OAI

end
end

section
section
namespace OAI

/-!
# Sorting finite subdivisions of the unit interval

Sorting a finite set containing the endpoints produces a genuine subdivision.
If that set also contains the knots of an earlier subdivision, every new
closed piece is contained in an old closed piece.
-/

namespace ThompsonNonamenability

structure SortedSubdivision (S : Finset UnitInterval) where
  pieceCount : ℕ
  positive : 0 < pieceCount
  knots : Fin (pieceCount + 1) → UnitInterval
  strictMono_knots : StrictMono knots
  first : knots 0 = unitIntervalZero
  last : knots (Fin.last pieceCount) = unitIntervalOne
  cover : ∀ x : UnitInterval, ∃ i : Fin pieceCount,
    knots i.castSucc ≤ x ∧ x ≤ knots i.succ
  knots_mem : ∀ i, knots i ∈ S
  contains : ∀ x ∈ S, ∃ i, knots i = x

namespace SortedSubdivision

/-- The adjacent closed intervals cover the unit interval. Monotonicity is not
needed for this auxiliary fact: take the last left endpoint below the point. -/
theorem cover_of_endpoints {n : ℕ} (hn : 0 < n)
    (knots : Fin (n + 1) → UnitInterval)
    (hfirst : knots 0 = unitIntervalZero)
    (hlast : knots (Fin.last n) = unitIntervalOne) (x : UnitInterval) :
    ∃ i : Fin n, knots i.castSucc ≤ x ∧ x ≤ knots i.succ := by
  classical
  let A : Finset (Fin n) := Finset.univ.filter (fun i => knots i.castSucc ≤ x)
  let i₀ : Fin n := ⟨0, hn⟩
  have hi₀ : i₀.castSucc = 0 := by apply Fin.ext; rfl
  have hA : A.Nonempty := by
    refine ⟨i₀, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    rw [hi₀, hfirst]
    exact x.property.1
  let i : Fin n := A.max' hA
  have hiA : i ∈ A := A.max'_mem hA
  refine ⟨i, (Finset.mem_filter.mp hiA).2, ?_⟩
  by_contra h
  have hlt : knots i.succ < x := lt_of_not_ge h
  have hisucc : i.val + 1 < n := by
    by_contra hbound
    have heq : i.succ = Fin.last n := by
      apply Fin.ext
      simp only [Fin.val_succ, Fin.val_last]
      have := i.isLt
      omega
    rw [heq, hlast] at hlt
    exact (not_lt_of_ge x.property.2) hlt
  let j : Fin n := ⟨i.val + 1, hisucc⟩
  have hjcast : j.castSucc = i.succ := by apply Fin.ext; rfl
  have hjA : j ∈ A := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [hjcast]
    exact hlt.le
  have hji : j ≤ i := A.le_max' j hjA
  change i.val + 1 ≤ i.val at hji
  omega

/-- Increasing enumeration of the actual finite knot set. -/
noncomputable def ofFinset (S : Finset UnitInterval)
    (h0 : unitIntervalZero ∈ S) (h1 : unitIntervalOne ∈ S) :
    SortedSubdivision S := by
  classical
  have hne : unitIntervalZero ≠ unitIntervalOne := by
    intro h
    have hv := congrArg (fun x : UnitInterval => (x : ℝ)) h
    exact zero_ne_one hv
  have hcard : 1 < S.card :=
    Finset.one_lt_card.mpr ⟨unitIntervalZero, h0, unitIntervalOne, h1, hne⟩
  let n := S.card - 1
  have hn : 0 < n := by dsimp [n]; omega
  have hc : S.card = n + 1 := by dsimp [n]; omega
  let e : Fin (n + 1) ↪o UnitInterval := S.orderEmbOfFin hc
  have hcontains : ∀ x ∈ S, ∃ i, e i = x := by
    intro x hx
    refine ⟨(S.orderIsoOfFin hc).symm ⟨x, hx⟩, ?_⟩
    exact congrArg Subtype.val ((S.orderIsoOfFin hc).apply_symm_apply ⟨x, hx⟩)
  have hfirst : e 0 = unitIntervalZero := by
    obtain ⟨j, hj⟩ := hcontains unitIntervalZero h0
    apply le_antisymm
    · calc
        e 0 ≤ e j := e.monotone (Fin.zero_le j)
        _ = unitIntervalZero := hj
    · exact (e 0).property.1
  have hlast : e (Fin.last n) = unitIntervalOne := by
    obtain ⟨j, hj⟩ := hcontains unitIntervalOne h1
    apply le_antisymm
    · exact (e (Fin.last n)).property.2
    · calc
        unitIntervalOne = e j := hj.symm
        _ ≤ e (Fin.last n) := e.monotone (Fin.le_last j)
  exact
    { pieceCount := n
      positive := hn
      knots := e
      strictMono_knots := e.strictMono
      first := hfirst
      last := hlast
      cover := cover_of_endpoints hn e hfirst hlast
      knots_mem := S.orderEmbOfFin_mem hc
      contains := hcontains }

/-- No point of the sorted knot set lies strictly between successive knots. -/
theorem no_mem_between {S : Finset UnitInterval} (r : SortedSubdivision S)
    (i : Fin r.pieceCount) {x : UnitInterval} (hx : x ∈ S) :
    ¬ (r.knots i.castSucc < x ∧ x < r.knots i.succ) := by
  obtain ⟨j, rfl⟩ := r.contains x hx
  intro h
  have hleft := r.strictMono_knots.lt_iff_lt.mp h.1
  have hright := r.strictMono_knots.lt_iff_lt.mp h.2
  change i.val < j.val at hleft
  change j.val < i.val + 1 at hright
  exact (not_lt_of_ge (Nat.succ_le_of_lt hleft)) hright

/-- A refinement containing every original knot has each closed piece inside
one original closed piece. The interior point selects a piece even when a
refined endpoint is itself an original knot. -/
theorem adjacent_contained {S : Finset UnitInterval} (r : SortedSubdivision S)
    {n : ℕ} (old : Fin (n + 1) → UnitInterval) (_hold : StrictMono old)
    (hcover : ∀ x : UnitInterval, ∃ j : Fin n,
      old j.castSucc ≤ x ∧ x ≤ old j.succ)
    (hmem : ∀ j, old j ∈ S) (i : Fin r.pieceCount) :
    ∃ j : Fin n, old j.castSucc ≤ r.knots i.castSucc ∧
      r.knots i.succ ≤ old j.succ := by
  have hlt : (r.knots i.castSucc : ℝ) < (r.knots i.succ : ℝ) :=
    r.strictMono_knots (Fin.castSucc_lt_succ_iff.mpr le_rfl)
  obtain ⟨y, hleft, hright⟩ := exists_between hlt
  let x : UnitInterval := ⟨y,
    (r.knots i.castSucc).property.1.trans hleft.le,
    hright.le.trans (r.knots i.succ).property.2⟩
  have hlx : r.knots i.castSucc < x := hleft
  have hxr : x < r.knots i.succ := hright
  obtain ⟨j, hjleft, hjright⟩ := hcover x
  refine ⟨j, ?_, ?_⟩
  · by_contra h
    exact r.no_mem_between i (hmem j.castSucc)
      ⟨lt_of_not_ge h, hjleft.trans_lt hxr⟩
  · by_contra h
    exact r.no_mem_between i (hmem j.succ)
      ⟨hlx.trans_le hjright, lt_of_not_ge h⟩

end SortedSubdivision

end ThompsonNonamenability

end OAI

end
end

section
section
namespace OAI

/-!
# Composition by a finite common subdivision

For `h ∘ g`, take every knot of `g` and the inverse image under `g` of every
knot of `h`.  Consecutive points of their sorted union lie in one piece of
`g` and map into one piece of `h`.  The two genuine affine equalities then
compose, adding their integer slope exponents.
-/

namespace ThompsonNonamenability
namespace DyadicPLWitness

/-- Composition of actual finite dyadic PL witnesses, using the sorted union
of the inner breakpoints and pulled-back outer breakpoints. -/
noncomputable def mul {h g : IntervalHomeomorph}
    (wh : DyadicPLWitness h) (wg : DyadicPLWitness g)
    (_hhmono : StrictMono h) (hgmono : StrictMono g) : DyadicPLWitness (h * g) := by
  classical
  let s : Finset UnitInterval := Finset.univ.image wg.knots ∪
    Finset.univ.image (fun j => g⁻¹ (wh.knots j))
  have hgmem (j : Fin (wg.pieceCount + 1)) : wg.knots j ∈ s := by
    exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩)
  have hhmem (j : Fin (wh.pieceCount + 1)) : g⁻¹ (wh.knots j) ∈ s := by
    exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩)
  have hs0 : unitIntervalZero ∈ s := by simpa only [wg.first] using hgmem 0
  have hs1 : unitIntervalOne ∈ s := by
    simpa only [wg.last] using hgmem (Fin.last wg.pieceCount)
  let r := SortedSubdivision.ofFinset s hs0 hs1
  have hgPieces (i : Fin r.pieceCount) : ∃ j : Fin wg.pieceCount,
      wg.knots j.castSucc ≤ r.knots i.castSucc ∧
        r.knots i.succ ≤ wg.knots j.succ :=
    r.adjacent_contained wg.knots wg.strictMono_knots wg.cover hgmem i
  have hhcover (x : UnitInterval) : ∃ j : Fin wh.pieceCount,
      g⁻¹ (wh.knots j.castSucc) ≤ x ∧ x ≤ g⁻¹ (wh.knots j.succ) := by
    obtain ⟨j, hj0, hj1⟩ := wh.cover (g x)
    refine ⟨j, ?_, ?_⟩
    · simpa only [IntervalHomeomorph.inv_apply_apply] using
        (IntervalHomeomorph.strictMono_inv hgmono).monotone hj0
    · simpa only [IntervalHomeomorph.inv_apply_apply] using
        (IntervalHomeomorph.strictMono_inv hgmono).monotone hj1
  have hhPieces (i : Fin r.pieceCount) : ∃ j : Fin wh.pieceCount,
      g⁻¹ (wh.knots j.castSucc) ≤ r.knots i.castSucc ∧
        r.knots i.succ ≤ g⁻¹ (wh.knots j.succ) :=
    r.adjacent_contained (fun j => g⁻¹ (wh.knots j))
      ((IntervalHomeomorph.strictMono_inv hgmono).comp wh.strictMono_knots)
      hhcover hhmem i
  let gi (i : Fin r.pieceCount) := Classical.choose (hgPieces i)
  let hi (i : Fin r.pieceCount) := Classical.choose (hhPieces i)
  have hgi (i : Fin r.pieceCount) :
      wg.knots (gi i).castSucc ≤ r.knots i.castSucc ∧
        r.knots i.succ ≤ wg.knots (gi i).succ := Classical.choose_spec (hgPieces i)
  have hhi (i : Fin r.pieceCount) :
      g⁻¹ (wh.knots (hi i).castSucc) ≤ r.knots i.castSucc ∧
        r.knots i.succ ≤ g⁻¹ (wh.knots (hi i).succ) :=
    Classical.choose_spec (hhPieces i)
  refine {
    pieceCount := r.pieceCount
    positive := r.positive
    knots := r.knots
    strictMono_knots := r.strictMono_knots
    first := r.first
    last := r.last
    dyadic := ?_
    cover := r.cover
    exponent := fun i => wh.exponent (hi i) + wg.exponent (gi i)
    affine := ?_ }
  · intro i
    have hmem := r.knots_mem i
    rcases Finset.mem_union.mp hmem with hmem | hmem
    · obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hmem
      rw [← hj]
      exact wg.dyadic j
    · obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hmem
      rw [← hj]
      exact (wg.inverse hgmono).map_dyadic
        (IntervalHomeomorph.strictMono_inv hgmono) (wh.dyadic j)
  · intro i x hx0 hx1
    have hab : r.knots i.castSucc ≤ r.knots i.succ :=
      (r.strictMono_knots (Fin.castSucc_lt_succ_iff.mpr le_rfl)).le
    have hga0 : wh.knots (hi i).castSucc ≤ g (r.knots i.castSucc) := by
      simpa only [IntervalHomeomorph.apply_inv_apply] using
        hgmono.monotone (hhi i).1
    have hgb1 : g (r.knots i.succ) ≤ wh.knots (hi i).succ := by
      simpa only [IntervalHomeomorph.apply_inv_apply] using
        hgmono.monotone (hhi i).2
    have hgx := wg.affine (gi i) x ((hgi i).1.trans hx0) (hx1.trans (hgi i).2)
    have hga := wg.affine (gi i) (r.knots i.castSucc)
      (hgi i).1 (hab.trans (hgi i).2)
    have hhgx := wh.affine (hi i) (g x)
      (hga0.trans (hgmono.monotone hx0)) ((hgmono.monotone hx1).trans hgb1)
    have hhga := wh.affine (hi i) (g (r.knots i.castSucc))
      hga0 ((hgmono.monotone hab).trans hgb1)
    simp only [IntervalHomeomorph.mul_apply]
    rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    rw [hhgx, hhga, hgx, hga]
    ring

end DyadicPLWitness

theorem HasDyadicPLPieces.mul {h g : IntervalHomeomorph}
    (hh : HasDyadicPLPieces h) (hg : HasDyadicPLPieces g)
    (hhmono : StrictMono h) (hgmono : StrictMono g) : HasDyadicPLPieces (h * g) := by
  obtain ⟨wh⟩ := hh
  obtain ⟨wg⟩ := hg
  exact ⟨wh.mul wg hhmono hgmono⟩

end ThompsonNonamenability

end OAI

end
end

section
section
namespace OAI

namespace ThompsonNonamenability

def standardSubgroup : Subgroup IntervalHomeomorph where
  carrier := {f | StrictMono f ∧ HasDyadicPLPieces f}
  one_mem' := ⟨fun _ _ h => h, hasDyadicPLPieces_one⟩
  mul_mem' hh hg :=
    ⟨hh.1.comp hg.1, hh.2.mul hg.2 hh.1 hg.1⟩
  inv_mem' hg :=
    ⟨IntervalHomeomorph.strictMono_inv hg.1, hg.2.inv hg.1⟩

namespace F

instance : Group F := inferInstanceAs (Group standardSubgroup)

@[simp] theorem one_apply (x : UnitInterval) : (1 : F) x = x := rfl

@[simp] theorem mul_apply (h g : F) (x : UnitInterval) : (h * g) x = h (g x) := rfl

@[simp] theorem inv_apply_apply (g : F) (x : UnitInterval) : g⁻¹ (g x) = x :=
  IntervalHomeomorph.inv_apply_apply g.toIntervalHomeomorph x

@[simp] theorem apply_inv_apply (g : F) (x : UnitInterval) : g (g⁻¹ x) = x :=
  IntervalHomeomorph.apply_inv_apply g.toIntervalHomeomorph x

end F

end ThompsonNonamenability

end OAI

end
end

section
section
namespace OAI

/-!
# Identification with the standard finite-breakpoint PL definition

The standard condition below states only a finite strictly ordered list of
dyadic knots, the two endpoints, and the powers-of-two affine formulas.
Coverage is derived from the endpoints; it is not an additional premise.
-/

namespace ThompsonNonamenability

/-- The usual increasing PL interval homeomorphisms with finitely many dyadic
breakpoints and slopes in the integer powers of two. -/
def StandardPLCondition (f : UnitInterval ≃ₜ UnitInterval) : Prop :=
  StrictMono f ∧ ∃ n : ℕ, 0 < n ∧
    ∃ knots : Fin (n + 1) → UnitInterval,
      StrictMono knots ∧
      knots 0 = unitIntervalZero ∧
      knots (Fin.last n) = unitIntervalOne ∧
      (∀ i, IsDyadic (knots i : ℝ)) ∧
      ∃ exponent : Fin n → ℤ,
        ∀ (i : Fin n) (x : UnitInterval),
          knots i.castSucc ≤ x → x ≤ knots i.succ →
          (f x : ℝ) = (f (knots i.castSucc) : ℝ) +
            (2 : ℝ) ^ exponent i * ((x : ℝ) - (knots i.castSucc : ℝ))

theorem intervalHomeomorph_standardPL_iff (f : IntervalHomeomorph) :
    (StrictMono f ∧ HasDyadicPLPieces f) ↔ StandardPLCondition f.toHomeomorph := by
  constructor
  · rintro ⟨hf, ⟨w⟩⟩
    exact ⟨hf, w.pieceCount, w.positive, w.knots, w.strictMono_knots,
      w.first, w.last, w.dyadic, w.exponent, w.affine⟩
  · rintro ⟨hf, n, hn, knots, hmono, hfirst, hlast, hdyadic, exponent, haffine⟩
    refine ⟨hf, ⟨?_⟩⟩
    exact {
      pieceCount := n
      positive := hn
      knots := knots
      strictMono_knots := hmono
      first := hfirst
      last := hlast
      dyadic := hdyadic
      cover := SortedSubdivision.cover_of_endpoints hn knots hfirst hlast
      exponent := exponent
      affine := haffine }

namespace F

theorem standardPLCondition (g : F) : StandardPLCondition g.toHomeomorph :=
  (intervalHomeomorph_standardPL_iff g.toIntervalHomeomorph).mp g.property

/-- A faithful identification with the standard PL group carrier, with no
uniform-grid or transport assumption in the right-hand side. -/
def standardPLEquiv : F ≃ {f : UnitInterval ≃ₜ UnitInterval // StandardPLCondition f} where
  toFun g := ⟨g.toHomeomorph, g.standardPLCondition⟩
  invFun f := ⟨⟨f.val⟩, (intervalHomeomorph_standardPL_iff ⟨f.val⟩).mpr f.property⟩
  left_inv g := by
    apply F.ext
    intro x
    rfl
  right_inv f := by
    apply Subtype.ext
    rfl

@[simp] theorem standardPLEquiv_apply (g : F) :
    (standardPLEquiv g).val = g.toHomeomorph := rfl

end F

end ThompsonNonamenability

end OAI

end
end

section
section
namespace OAI

/-!
# Basic dyadic intervals

A cell records its actual depth and its index on that dyadic grid.  Its
endpoints determine the record uniquely.  Composition is the affine image of
one cell inside another; no formal interval identifications are assumed.
-/

noncomputable section

namespace ThompsonNonamenability

structure BasicInterval where
  depth : ℕ
  index : Fin (2 ^ depth)
  deriving DecidableEq

namespace BasicInterval

@[ext] theorem ext_depth_index {I J : BasicInterval}
    (hd : I.depth = J.depth) (hi : I.index.val = J.index.val) : I = J := by
  cases I with
  | mk d i =>
    cases J with
    | mk e j =>
      dsimp at hd hi
      subst e
      have hij : i = j := Fin.ext hi
      subst j
      rfl

def left (I : BasicInterval) : ℝ := (I.index.val : ℝ) / (2 : ℝ) ^ I.depth

def right (I : BasicInterval) : ℝ := ((I.index.val : ℝ) + 1) / (2 : ℝ) ^ I.depth

def length (I : BasicInterval) : ℝ := ((2 : ℝ) ^ I.depth)⁻¹

def carrier (I : BasicInterval) : Set ℝ := Set.Icc I.left I.right

def interior (I : BasicInterval) : Set ℝ := Set.Ioo I.left I.right

def Internal (I : BasicInterval) : Prop := 0 < I.left ∧ I.right < 1

def Before (I J : BasicInterval) : Prop := I.right < J.left

def Contained (K I : BasicInterval) : Prop := I.left ≤ K.left ∧ K.right ≤ I.right

def chart (I : BasicInterval) (x : ℝ) : ℝ :=
  ((I.index.val : ℝ) + x) / (2 : ℝ) ^ I.depth

theorem denominator_pos (I : BasicInterval) : 0 < (2 : ℝ) ^ I.depth :=
  pow_pos (by norm_num) _

theorem denominator_ne_zero (I : BasicInterval) : (2 : ℝ) ^ I.depth ≠ 0 :=
  ne_of_gt I.denominator_pos

theorem length_pos (I : BasicInterval) : 0 < I.length :=
  inv_pos.mpr I.denominator_pos

theorem length_eq_right_sub_left (I : BasicInterval) :
    I.length = I.right - I.left := by
  unfold length right left
  ring

theorem left_nonneg (I : BasicInterval) : 0 ≤ I.left :=
  div_nonneg (Nat.cast_nonneg _) (le_of_lt I.denominator_pos)

theorem right_le_one (I : BasicInterval) : I.right ≤ 1 := by
  apply (div_le_one I.denominator_pos).2
  exact_mod_cast Nat.succ_le_of_lt I.index.isLt

theorem left_lt_right (I : BasicInterval) : I.left < I.right := by
  apply (div_lt_div_iff_of_pos_right I.denominator_pos).2
  linarith

theorem carrier_subset_unit (I : BasicInterval) : I.carrier ⊆ Set.Icc (0 : ℝ) 1 := by
  intro x hx
  exact ⟨I.left_nonneg.trans hx.1, hx.2.trans I.right_le_one⟩

theorem interior_subset_carrier (I : BasicInterval) : I.interior ⊆ I.carrier := by
  intro x hx
  exact ⟨hx.1.le, hx.2.le⟩

theorem contained_refl (I : BasicInterval) : I.Contained I := ⟨le_rfl, le_rfl⟩

theorem Contained.trans {I J K : BasicInterval}
    (hIJ : I.Contained J) (hJK : J.Contained K) : I.Contained K :=
  ⟨hJK.1.trans hIJ.1, hIJ.2.trans hJK.2⟩

theorem length_le_of_contained {I J : BasicInterval} (h : I.Contained J) :
    I.length ≤ J.length := by
  rw [length_eq_right_sub_left, length_eq_right_sub_left]
  exact sub_le_sub h.2 h.1

@[simp] theorem chart_zero (I : BasicInterval) : I.chart 0 = I.left := by
  simp [chart, left]

@[simp] theorem chart_one (I : BasicInterval) : I.chart 1 = I.right := rfl

theorem chart_eq_left_add_length_mul (I : BasicInterval) (x : ℝ) :
    I.chart x = I.left + I.length * x := by
  unfold chart left length
  ring

theorem chart_strictMono (I : BasicInterval) : StrictMono I.chart := by
  intro x y hxy
  apply (div_lt_div_iff_of_pos_right I.denominator_pos).2
  exact add_lt_add_right hxy _

theorem chart_mem_self_carrier_iff (I : BasicInterval) (x : ℝ) :
    I.chart x ∈ I.carrier ↔ x ∈ Set.Icc (0 : ℝ) 1 := by
  change I.left ≤ I.chart x ∧ I.chart x ≤ I.right ↔ 0 ≤ x ∧ x ≤ 1
  rw [← I.chart_zero, ← I.chart_one]
  simp only [I.chart_strictMono.le_iff_le]

theorem ext_endpoints {I J : BasicInterval}
    (hl : I.left = J.left) (hr : I.right = J.right) : I = J := by
  have hlen : I.length = J.length := by
    rw [length_eq_right_sub_left, length_eq_right_sub_left, hl, hr]
  have hp : (2 : ℝ) ^ I.depth = (2 : ℝ) ^ J.depth := inv_injective hlen
  have hd : I.depth = J.depth :=
    (pow_right_inj₀ (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1)).1 hp
  apply ext_depth_index hd
  have hdiv : (I.index.val : ℝ) / (2 : ℝ) ^ J.depth =
      (J.index.val : ℝ) / (2 : ℝ) ^ J.depth := by
    simpa only [left, hd] using hl
  have hi : (I.index.val : ℝ) = (J.index.val : ℝ) :=
    (div_left_inj' J.denominator_ne_zero).1 hdiv
  exact_mod_cast hi

def root : BasicInterval := ⟨0, ⟨0, by norm_num⟩⟩

@[simp] theorem root_depth : root.depth = 0 := rfl

@[simp] theorem root_index : root.index.val = 0 := rfl

@[simp] theorem root_left : root.left = 0 := by norm_num [root, left]

@[simp] theorem root_right : root.right = 1 := by norm_num [root, right]

@[simp] theorem root_length : root.length = 1 := by norm_num [root, length]

@[simp] theorem root_chart (x : ℝ) : root.chart x = x := by simp [root, chart]

def comp (I J : BasicInterval) : BasicInterval where
  depth := I.depth + J.depth
  index := ⟨I.index.val * 2 ^ J.depth + J.index.val, by
    have hI : I.index.val + 1 ≤ 2 ^ I.depth := Nat.succ_le_of_lt I.index.isLt
    calc
      I.index.val * 2 ^ J.depth + J.index.val <
          I.index.val * 2 ^ J.depth + 2 ^ J.depth := Nat.add_lt_add_left J.index.isLt _
      _ = (I.index.val + 1) * 2 ^ J.depth := by ring
      _ ≤ 2 ^ I.depth * 2 ^ J.depth := Nat.mul_le_mul_right _ hI
      _ = 2 ^ (I.depth + J.depth) := (pow_add _ _ _).symm⟩

@[simp] theorem comp_depth (I J : BasicInterval) : (I.comp J).depth = I.depth + J.depth := rfl

@[simp] theorem comp_index (I J : BasicInterval) :
    (I.comp J).index.val = I.index.val * 2 ^ J.depth + J.index.val := rfl

theorem chart_comp (I J : BasicInterval) (x : ℝ) :
    (I.comp J).chart x = I.chart (J.chart x) := by
  simp only [chart, comp_depth, comp_index, Nat.cast_add, Nat.cast_mul,
    Nat.cast_pow, Nat.cast_ofNat, pow_add]
  field_simp
  ring

theorem left_comp (I J : BasicInterval) : (I.comp J).left = I.chart J.left := by
  rw [← chart_zero, chart_comp, chart_zero]

theorem right_comp (I J : BasicInterval) : (I.comp J).right = I.chart J.right := by
  rw [← chart_one, chart_comp, chart_one]

theorem comp_assoc (I J K : BasicInterval) : (I.comp J).comp K = I.comp (J.comp K) := by
  apply ext_depth_index
  · simp only [comp_depth, Nat.add_assoc]
  · simp only [comp_index, comp_depth, pow_add]
    ring

@[simp] theorem comp_root (I : BasicInterval) : I.comp root = I := by
  apply ext_depth_index <;> simp

@[simp] theorem root_comp (I : BasicInterval) : root.comp I = I := by
  apply ext_depth_index <;> simp

theorem comp_left_injective (I : BasicInterval) : Function.Injective I.comp := by
  intro J K h
  have hd : J.depth = K.depth := Nat.add_left_cancel (congrArg depth h)
  apply ext_depth_index hd
  have hi := congrArg (fun C : BasicInterval => C.index.val) h
  simp only [comp_index, hd] at hi
  exact Nat.add_left_cancel hi

theorem comp_injective (I : BasicInterval) : Function.Injective I.comp :=
  comp_left_injective I

theorem comp_contained (I J : BasicInterval) : (I.comp J).Contained I := by
  constructor
  · rw [left_comp, ← I.chart_zero]
    exact I.chart_strictMono.monotone J.left_nonneg
  · rw [right_comp, ← I.chart_one]
    exact I.chart_strictMono.monotone J.right_le_one

theorem chart_mem_carrier_iff (I J : BasicInterval) (x : ℝ) :
    I.chart x ∈ (I.comp J).carrier ↔ x ∈ J.carrier := by
  simp only [carrier, Set.mem_Icc, left_comp, right_comp, I.chart_strictMono.le_iff_le]

theorem chart_mem_interior_iff (I J : BasicInterval) (x : ℝ) :
    I.chart x ∈ (I.comp J).interior ↔ x ∈ J.interior := by
  simp only [interior, Set.mem_Ioo, left_comp, right_comp, I.chart_strictMono.lt_iff_lt]

theorem comp_contained_iff (I J K : BasicInterval) :
    (I.comp J).Contained (I.comp K) ↔ J.Contained K := by
  simp only [Contained, left_comp, right_comp, I.chart_strictMono.le_iff_le]

theorem comp_internal_of_internal_right (I J : BasicInterval) (hJ : J.Internal) :
    (I.comp J).Internal := by
  constructor
  · rw [left_comp]
    have h := I.chart_strictMono hJ.1
    rw [chart_zero] at h
    exact I.left_nonneg.trans_lt h
  · rw [right_comp]
    have h := I.chart_strictMono hJ.2
    rw [chart_one] at h
    exact h.trans_le I.right_le_one

theorem comp_before_comp (I : BasicInterval) {J K : BasicInterval} (h : J.Before K) :
    (I.comp J).Before (I.comp K) := by
  change (I.comp J).right < (I.comp K).left
  rw [right_comp, left_comp]
  exact I.chart_strictMono h

end BasicInterval

end ThompsonNonamenability

end

end OAI

end
end

section
section
namespace OAI

/-!
# Nesting and normalization of basic dyadic intervals

The endpoint comparisons are made on a common dyadic grid. In particular,
intersecting open interiors force one basic interval to contain the other.
-/

noncomputable section

namespace ThompsonNonamenability.BasicInterval

open Set

/-- Express a left endpoint on any finer dyadic grid. -/
theorem left_eq_on_finer_grid (I : BasicInterval) {s : ℕ} (h : I.depth ≤ s) :
    I.left = ((I.index.val * 2 ^ (s - I.depth) : ℕ) : ℝ) / (2 : ℝ) ^ s := by
  have hp : (2 : ℝ) ^ s = (2 : ℝ) ^ I.depth * (2 : ℝ) ^ (s - I.depth) := by
    rw [← pow_add, Nat.add_sub_cancel' h]
  have hI : (2 : ℝ) ^ I.depth ≠ 0 := by positivity
  have hD : (2 : ℝ) ^ (s - I.depth) ≠ 0 := by positivity
  simp only [left, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, hp]
  field_simp [hI, hD]

/-- Express a right endpoint on any finer dyadic grid. -/
theorem right_eq_on_finer_grid (I : BasicInterval) {s : ℕ} (h : I.depth ≤ s) :
    I.right = (((I.index.val + 1) * 2 ^ (s - I.depth) : ℕ) : ℝ) /
      (2 : ℝ) ^ s := by
  have hp : (2 : ℝ) ^ s = (2 : ℝ) ^ I.depth * (2 : ℝ) ^ (s - I.depth) := by
    rw [← pow_add, Nat.add_sub_cancel' h]
  have hI : (2 : ℝ) ^ I.depth ≠ 0 := by positivity
  have hD : (2 : ℝ) ^ (s - I.depth) ≠ 0 := by positivity
  simp only [right, Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_pow,
    Nat.cast_ofNat, hp]
  field_simp [hI, hD]

/-- A contained basic interval has at least the depth of its container. -/
theorem depth_le_of_contained {I K : BasicInterval} (h : K.Contained I) :
    I.depth ≤ K.depth := by
  have hl := length_le_of_contained h
  change ((2 : ℝ) ^ K.depth)⁻¹ ≤ ((2 : ℝ) ^ I.depth)⁻¹ at hl
  have hp : (2 : ℝ) ^ I.depth ≤ (2 : ℝ) ^ K.depth :=
    (inv_le_inv₀ (by positivity) (by positivity)).mp hl
  exact (pow_le_pow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mp hp

/-- Containment gives the integer endpoint bounds on the finer grid. -/
theorem index_bounds_of_contained {I K : BasicInterval} (h : K.Contained I) :
    I.index.val * 2 ^ (K.depth - I.depth) ≤ K.index.val ∧
      K.index.val + 1 ≤ (I.index.val + 1) * 2 ^ (K.depth - I.depth) := by
  have hd := depth_le_of_contained h
  have hp : 0 < (2 : ℝ) ^ K.depth := by positivity
  have hl := h.1
  have hr := h.2
  rw [left_eq_on_finer_grid I hd, left] at hl
  rw [right_eq_on_finer_grid I hd, right] at hr
  constructor
  · exact_mod_cast (div_le_div_iff_of_pos_right hp).mp hl
  · exact_mod_cast (div_le_div_iff_of_pos_right hp).mp hr

/-- A subinterval is precisely the image of a basic interval under the
container's affine chart. -/
theorem contained_iff_exists_comp {I K : BasicInterval} :
    K.Contained I ↔ ∃ J : BasicInterval, I.comp J = K := by
  constructor
  · intro h
    have hd := depth_le_of_contained h
    obtain ⟨hl, hr⟩ := index_bounds_of_contained h
    have hn : K.index.val - I.index.val * 2 ^ (K.depth - I.depth) <
        2 ^ (K.depth - I.depth) := by
      rw [Nat.add_mul, Nat.one_mul] at hr
      omega
    let J : BasicInterval :=
      ⟨K.depth - I.depth, ⟨K.index.val - I.index.val * 2 ^ (K.depth - I.depth), hn⟩⟩
    refine ⟨J, ext_depth_index ?_ ?_⟩
    · change I.depth + (K.depth - I.depth) = K.depth
      omega
    · change I.index.val * 2 ^ (K.depth - I.depth) +
          (K.index.val - I.index.val * 2 ^ (K.depth - I.depth)) = K.index.val
      omega
  · rintro ⟨J, rfl⟩
    exact comp_contained I J

/-- The basic interval obtained by applying the inverse chart of `I` to `K`. -/
def normalize (I K : BasicInterval) (h : K.Contained I) : BasicInterval :=
  Classical.choose (contained_iff_exists_comp.mp h)

theorem comp_normalize (I K : BasicInterval) (h : K.Contained I) :
    I.comp (normalize I K h) = K :=
  Classical.choose_spec (contained_iff_exists_comp.mp h)

@[simp] theorem normalize_comp (I J : BasicInterval) (h : (I.comp J).Contained I) :
    normalize I (I.comp J) h = J := by
  apply comp_injective I
  exact comp_normalize I (I.comp J) h

/-- At ordered depths, overlap of open interiors implies containment. -/
theorem contained_of_overlap_of_depth_le {I K : BasicInterval}
    (hd : I.depth ≤ K.depth) (h : (I.interior ∩ K.interior).Nonempty) :
    K.Contained I := by
  obtain ⟨x, hxI, hxK⟩ := h
  have hl : I.left < K.right := lt_trans hxI.1 hxK.2
  have hr : K.left < I.right := lt_trans hxK.1 hxI.2
  have hp : 0 < (2 : ℝ) ^ K.depth := by positivity
  rw [left_eq_on_finer_grid I hd, right] at hl
  rw [right_eq_on_finer_grid I hd, left] at hr
  have hln : I.index.val * 2 ^ (K.depth - I.depth) < K.index.val + 1 := by
    exact_mod_cast (div_lt_div_iff_of_pos_right hp).mp hl
  have hrn : K.index.val < (I.index.val + 1) * 2 ^ (K.depth - I.depth) := by
    exact_mod_cast (div_lt_div_iff_of_pos_right hp).mp hr
  have hl' : I.index.val * 2 ^ (K.depth - I.depth) ≤ K.index.val := by omega
  have hr' : K.index.val + 1 ≤ (I.index.val + 1) * 2 ^ (K.depth - I.depth) := by omega
  constructor
  · rw [left_eq_on_finer_grid I hd, left]
    apply (div_le_div_iff_of_pos_right hp).mpr
    exact_mod_cast hl'
  · rw [right_eq_on_finer_grid I hd, right]
    apply (div_le_div_iff_of_pos_right hp).mpr
    exact_mod_cast hr'

/-- Basic dyadic intervals with intersecting open interiors are nested. -/
theorem overlap_interior_nested {I J : BasicInterval}
    (h : (I.interior ∩ J.interior).Nonempty) : I.Contained J ∨ J.Contained I := by
  rcases le_total I.depth J.depth with hd | hd
  · exact Or.inr (contained_of_overlap_of_depth_le hd h)
  · apply Or.inl
    apply contained_of_overlap_of_depth_le hd
    simpa only [inter_comm] using h

end ThompsonNonamenability.BasicInterval

end

end OAI

end
end

section
section
namespace OAI

/-!
# Finite partitions into basic dyadic intervals

Closed cells cover the unit interval; their open interiors are disjoint.
Restriction is the actual inverse image of the cell set under affine insertion.
-/

noncomputable section

namespace ThompsonNonamenability

open Set

structure BasicPartition where
  cells : Finset BasicInterval
  cover : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∃ I ∈ cells, x ∈ I.carrier
  disjoint : (cells : Set BasicInterval).Pairwise
    (fun I J => Disjoint I.interior J.interior)

namespace BasicPartition

@[ext]
theorem ext {T U : BasicPartition} (h : T.cells = U.cells) : T = U := by
  cases T
  cases U
  cases h
  rfl

def cellCount (T : BasicPartition) : ℕ := T.cells.card

/-- The interval is exactly covered by partition cells contained in it. -/
def Respects (T : BasicPartition) (I : BasicInterval) : Prop :=
  ∀ x ∈ I.carrier, ∃ K ∈ T.cells, K.Contained I ∧ x ∈ K.carrier

private theorem interiors_overlap_of_mem_interior_mem_carrier
    {I J : BasicInterval} {x : ℝ} (hxI : x ∈ I.interior)
    (hxJ : x ∈ J.carrier) : (I.interior ∩ J.interior).Nonempty := by
  have h : max I.left J.left < min I.right J.right := by
    apply lt_min
    · exact max_lt I.left_lt_right (lt_of_le_of_lt hxJ.1 hxI.2)
    · exact max_lt (lt_of_lt_of_le hxI.1 hxJ.2) J.left_lt_right
  obtain ⟨y, hy₁, hy₂⟩ := exists_between h
  exact ⟨y, ⟨lt_of_le_of_lt (le_max_left _ _) hy₁,
    lt_of_lt_of_le hy₂ (min_le_left _ _)⟩,
    ⟨lt_of_le_of_lt (le_max_right _ _) hy₁,
    lt_of_lt_of_le hy₂ (min_le_right _ _)⟩⟩

/-- At an interior point, even membership in another closed cell forces equality. -/
theorem eq_of_mem_interior_mem_carrier (T : BasicPartition)
    {I J : BasicInterval} (hI : I ∈ T.cells) (hJ : J ∈ T.cells)
    {x : ℝ} (hxI : x ∈ I.interior) (hxJ : x ∈ J.carrier) : I = J := by
  by_contra hne
  obtain ⟨y, hyI, hyJ⟩ := interiors_overlap_of_mem_interior_mem_carrier hxI hxJ
  exact Set.disjoint_left.mp (T.disjoint hI hJ hne) hyI hyJ

/-- Equivalent geometric crossing condition, including the endpoint argument. -/
theorem respects_iff (T : BasicPartition) (I : BasicInterval) :
    T.Respects I ↔ ∀ K ∈ T.cells,
      (K.interior ∩ I.interior).Nonempty → K.Contained I := by
  constructor
  · intro h K hK ⟨x, hxK, hxI⟩
    obtain ⟨L, hL, hLI, hxL⟩ := h x ⟨hxI.1.le, hxI.2.le⟩
    exact (T.eq_of_mem_interior_mem_carrier hK hL hxK hxL).symm ▸ hLI
  · intro h
    classical
    let contained := T.cells.filter (fun K => K.Contained I)
    let covered : Set ℝ := ⋃ K ∈ contained, K.carrier
    have hclosed : IsClosed covered := by
      apply isClosed_biUnion_finset
      intro K hK
      exact isClosed_Icc
    have hinterior : I.interior ⊆ covered := by
      intro x hxI
      have hxunit : x ∈ Set.Icc (0 : ℝ) 1 :=
        I.carrier_subset_unit ⟨hxI.1.le, hxI.2.le⟩
      obtain ⟨K, hK, hxK⟩ := T.cover x hxunit
      have hmeet : (K.interior ∩ I.interior).Nonempty := by
        obtain ⟨y, hyI, hyK⟩ :=
          interiors_overlap_of_mem_interior_mem_carrier hxI hxK
        exact ⟨y, hyK, hyI⟩
      have hKI := h K hK hmeet
      exact Set.mem_iUnion₂.mpr ⟨K, Finset.mem_filter.mpr ⟨hK, hKI⟩, hxK⟩
    have hcarrier : I.carrier ⊆ covered := by
      have hc := closure_minimal hinterior hclosed
      simpa only [BasicInterval.interior, BasicInterval.carrier,
        closure_Ioo I.left_lt_right.ne] using hc
    intro x hx
    obtain ⟨K, hK, hxK⟩ := Set.mem_iUnion₂.mp (hcarrier hx)
    exact ⟨K, (Finset.mem_filter.mp hK).1, (Finset.mem_filter.mp hK).2, hxK⟩

/-- A sufficiently fine actual partition respects the specified basic interval. -/
theorem respects_of_mesh_lt (T : BasicPartition) (I : BasicInterval)
    (hmesh : ∀ K ∈ T.cells, K.length < I.length) : T.Respects I := by
  apply (T.respects_iff I).mpr
  intro K hK hmeet
  rcases BasicInterval.overlap_interior_nested hmeet with hKI | hIK
  · exact hKI
  · have hlen : I.length ≤ K.length := by
      rw [I.length_eq_right_sub_left, K.length_eq_right_sub_left]
      exact sub_le_sub hIK.2 hIK.1
    exact False.elim (not_lt_of_ge hlen (hmesh K hK))

/-- Affinely normalized cells. Membership is exactly membership after insertion. -/
def restrictCells (T : BasicPartition) (I : BasicInterval) : Finset BasicInterval :=
  T.cells.preimage I.comp I.comp_left_injective.injOn

@[simp]
theorem mem_restrictCells (T : BasicPartition) (I J : BasicInterval) :
    J ∈ T.restrictCells I ↔ I.comp J ∈ T.cells :=
  Finset.mem_preimage

/-- The genuine partition obtained by restriction and affine normalization. -/
def restrict (T : BasicPartition) (I : BasicInterval) (h : T.Respects I) :
    BasicPartition where
  cells := T.restrictCells I
  cover := by
    intro x hx
    have hchart : I.chart x ∈ I.carrier :=
      (I.chart_mem_self_carrier_iff x).mpr hx
    obtain ⟨K, hK, hKI, hxK⟩ := h (I.chart x) hchart
    obtain ⟨J, hJ⟩ := BasicInterval.contained_iff_exists_comp.mp hKI
    refine ⟨J, (T.mem_restrictCells I J).mpr (hJ.symm ▸ hK), ?_⟩
    apply (I.chart_mem_carrier_iff J x).mp
    simpa only [hJ] using hxK
  disjoint := by
    intro J hJ K hK hne
    apply Set.disjoint_left.mpr
    intro x hxJ hxK
    have hJK : I.comp J ≠ I.comp K := fun heq => hne (I.comp_left_injective heq)
    exact Set.disjoint_left.mp
      (T.disjoint ((T.mem_restrictCells I J).mp hJ)
        ((T.mem_restrictCells I K).mp hK) hJK)
      ((I.chart_mem_interior_iff J x).mpr hxJ)
      ((I.chart_mem_interior_iff K x).mpr hxK)

@[simp]
theorem mem_restrict_cells (T : BasicPartition) (I : BasicInterval)
    (h : T.Respects I) (J : BasicInterval) :
    J ∈ (T.restrict I h).cells ↔ I.comp J ∈ T.cells :=
  T.mem_restrictCells I J

open Classical in
theorem restrict_cellCount_eq_filter_card (T : BasicPartition) (I : BasicInterval)
    (h : T.Respects I) :
    (T.restrict I h).cellCount = (T.cells.filter (fun K => K.Contained I)).card := by
  classical
  change (T.cells.preimage I.comp I.comp_left_injective.injOn).card = _
  rw [Finset.card_preimage]
  congr 1
  ext K
  simp only [Finset.mem_filter, Set.mem_range,
    ← BasicInterval.contained_iff_exists_comp]

theorem restrict_cellCount_lt (T : BasicPartition) (I : BasicInterval)
    (h : T.Respects I) (hI : I.Internal) :
    (T.restrict I h).cellCount < T.cellCount := by
  classical
  rw [T.restrict_cellCount_eq_filter_card I h]
  obtain ⟨K, hK, hxK⟩ := T.cover 0 ⟨le_rfl, zero_le_one⟩
  have hnot : ¬K.Contained I := by
    intro hKI
    have hle : I.left ≤ 0 := le_trans hKI.1 hxK.1
    exact (not_le_of_gt hI.1) hle
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨Finset.filter_subset _ _, ?_⟩
  intro heq
  have hf : K ∈ T.cells.filter (fun K => K.Contained I) := heq.symm ▸ hK
  exact hnot (Finset.mem_filter.mp hf).2

theorem restrict_respects (T : BasicPartition) (I J : BasicInterval)
    (hI : T.Respects I) (hIJ : T.Respects (I.comp J)) :
    (T.restrict I hI).Respects J := by
  intro x hx
  have hchart : I.chart x ∈ (I.comp J).carrier :=
    (I.chart_mem_carrier_iff J x).mpr hx
  obtain ⟨K, hK, hKIJ, hxK⟩ := hIJ (I.chart x) hchart
  have hKI : K.Contained I :=
    ⟨le_trans (I.comp_contained J).1 hKIJ.1,
      le_trans hKIJ.2 (I.comp_contained J).2⟩
  obtain ⟨L, hL⟩ := BasicInterval.contained_iff_exists_comp.mp hKI
  refine ⟨L, (T.mem_restrict_cells I hI L).mpr (hL.symm ▸ hK), ?_, ?_⟩
  · apply (I.comp_contained_iff L J).mp
    simpa only [hL] using hKIJ
  · apply (I.chart_mem_carrier_iff L x).mp
    simpa only [hL] using hxK

theorem restrict_restrict (T : BasicPartition) (I J : BasicInterval)
    (hI : T.Respects I) (hIJ : T.Respects (I.comp J)) :
    (T.restrict I hI).restrict J (T.restrict_respects I J hI hIJ) =
      T.restrict (I.comp J) hIJ := by
  apply BasicPartition.ext
  ext K
  simp only [mem_restrict_cells, BasicInterval.comp_assoc]

end BasicPartition

end ThompsonNonamenability

end

end OAI

end
end

section
section
namespace OAI


namespace ThompsonNonamenability

abbrev UnitBall (E : Type uE) [SeminormedAddCommGroup E] := {x : E // ‖x‖ ≤ 1}

def unitBallZero (E : Type uE) [SeminormedAddCommGroup E] : UnitBall E :=
  ⟨0, by simp⟩

@[simp] theorem coe_unitBallZero (E : Type uE) [SeminormedAddCommGroup E] :
    (unitBallZero E : E) = 0 := rfl

end ThompsonNonamenability

end OAI

end
end

section
section
namespace OAI

/-!
# Finite averages in the unit ball

The norm bounds hold in any real seminormed space. Inner-product expansions are
kept in a separate section and require a real inner-product space.
-/

noncomputable section

open scoped BigOperators InnerProductSpace


namespace ThompsonNonamenability

section Normed

variable {E : Type uE} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
variable {D : ℕ}

/-- The equally weighted mean of a finite family. -/
def finMean (x : Fin D → E) : E :=
  (D : ℝ)⁻¹ • ∑ i, x i

theorem finMean_sub (x y : Fin D → E) :
    finMean (fun i => x i - y i) = finMean x - finMean y := by
  simp only [finMean, Finset.sum_sub_distrib, smul_sub]

@[simp] theorem finMean_const (hD : 0 < D) (z : E) :
    finMean (fun _ : Fin D => z) = z := by
  have hD' : (D : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hD)
  rw [finMean, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    ← Nat.cast_smul_eq_nsmul ℝ D z, smul_smul, inv_mul_cancel₀ hD', one_smul]

/-- The squared norm of a mean is bounded by the mean of the squared norms. -/
theorem norm_finMean_sq_le (hD : 0 < D) (x : Fin D → E) :
    ‖finMean x‖ ^ 2 ≤ (D : ℝ)⁻¹ * ∑ i, ‖x i‖ ^ 2 := by
  have hD' : (D : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hD)
  have hc : 0 ≤ (D : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg D)
  have hcs : (∑ i, ‖x i‖) ^ 2 ≤ (D : ℝ) * ∑ i, ‖x i‖ ^ 2 := by
    simpa using Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun _ : Fin D => (1 : ℝ)) (fun i => ‖x i‖)
  have hs : ‖∑ i, x i‖ ^ 2 ≤ (D : ℝ) * ∑ i, ‖x i‖ ^ 2 :=
    (pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le Finset.univ x) 2).trans hcs
  calc
    ‖finMean x‖ ^ 2 = ((D : ℝ)⁻¹) ^ 2 * ‖∑ i, x i‖ ^ 2 := by
      rw [finMean, norm_smul_of_nonneg hc, mul_pow]
    _ ≤ ((D : ℝ)⁻¹) ^ 2 * ((D : ℝ) * ∑ i, ‖x i‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hs (sq_nonneg _)
    _ = (D : ℝ)⁻¹ * ((D : ℝ)⁻¹ * (D : ℝ)) * ∑ i, ‖x i‖ ^ 2 := by
      ring
    _ = (D : ℝ)⁻¹ * ∑ i, ‖x i‖ ^ 2 := by
      rw [inv_mul_cancel₀ hD', mul_one]

/-- Averaging a finite family in the closed unit ball preserves its norm bound. -/
theorem finMean_mem_unitBall (hD : 0 < D) (x : Fin D → UnitBall E) :
    ‖finMean (fun i => (x i : E))‖ ≤ 1 := by
  have hD' : (D : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hD)
  have hc : 0 ≤ (D : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg D)
  have hs : ‖∑ i, (x i : E)‖ ≤ (D : ℝ) := by
    calc
      ‖∑ i, (x i : E)‖ ≤ ∑ i, ‖(x i : E)‖ := norm_sum_le Finset.univ _
      _ ≤ ∑ _i : Fin D, (1 : ℝ) :=
        Finset.sum_le_sum (fun i _ => (x i).property)
      _ = (D : ℝ) := by simp
  calc
    ‖finMean (fun i => (x i : E))‖ = (D : ℝ)⁻¹ * ‖∑ i, (x i : E)‖ := by
      rw [finMean, norm_smul_of_nonneg hc]
    _ ≤ (D : ℝ)⁻¹ * (D : ℝ) := mul_le_mul_of_nonneg_left hs hc
    _ = 1 := inv_mul_cancel₀ hD'

/-- The equally weighted mean, bundled with its unit-ball bound. -/
def ballMean (hD : 0 < D) (x : Fin D → UnitBall E) : UnitBall E :=
  ⟨finMean (fun i => (x i : E)), finMean_mem_unitBall hD x⟩

@[simp] theorem coe_ballMean (hD : 0 < D) (x : Fin D → UnitBall E) :
    (ballMean hD x : E) = finMean (fun i => (x i : E)) := rfl

end Normed

section InnerProduct

variable {E : Type uE} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {D K : ℕ}

/-- The inner product of two finite averages is the average of all pairings. -/
theorem inner_finMean (x : Fin D → E) (y : Fin K → E) :
    ⟪finMean x, finMean y⟫_ℝ =
      ((D : ℝ)⁻¹ * (K : ℝ)⁻¹) * ∑ i, ∑ j, ⟪x i, y j⟫_ℝ := by
  simp_rw [finMean, real_inner_smul_left, real_inner_smul_right,
    sum_inner, inner_sum, mul_assoc]

/-- Expand the squared norm of an average into all pairwise inner products. -/
theorem norm_finMean_sq (x : Fin D → E) :
    ‖finMean x‖ ^ 2 = ((D : ℝ)⁻¹) ^ 2 * ∑ i, ∑ j, ⟪x i, x j⟫_ℝ := by
  rw [← real_inner_self_eq_norm_sq, inner_finMean, pow_two]

end InnerProduct

end ThompsonNonamenability

end

end OAI

end
end

section
section
namespace OAI

/-!
# Recursive unit-ball colors of actual basic dyadic partitions

The recursion uses the number of actual cells. Restriction to any selected
internal interval strictly decreases that number. The mean is bundled with
its genuine unit-ball proof before it is supplied to the map.
-/

noncomputable section


namespace ThompsonNonamenability

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {D : ℕ}

def partitionColor (I : Fin D → BasicInterval) (hI : ∀ i, (I i).Internal)
    (hD : 0 < D) (f : UnitBall E → UnitBall E) (T : BasicPartition) :
    UnitBall E := by
  classical
  exact if h : ∀ i, T.Respects (I i) then
    f (ballMean hD (fun i =>
      partitionColor I hI hD f (T.restrict (I i) (h i))))
  else unitBallZero E
termination_by T.cellCount
decreasing_by
  exact T.restrict_cellCount_lt _ _ (hI _)

/-- The recursive branch, with its actual restricted partitions. -/
theorem partitionColor_of_respects (I : Fin D → BasicInterval)
    (hI : ∀ i, (I i).Internal) (hD : 0 < D)
    (f : UnitBall E → UnitBall E) (T : BasicPartition)
    (h : ∀ i, T.Respects (I i)) :
    partitionColor I hI hD f T = f (ballMean hD (fun i =>
      partitionColor I hI hD f (T.restrict (I i) (h i)))) := by
  rw [partitionColor]
  simp only [dif_pos h]

/-- Applying the recursion to a parent restriction gives the actual child mean.
The normalized two-step restriction is replaced by the proved composite one. -/
theorem partitionColor_restrict (I : Fin D → BasicInterval)
    (hI : ∀ i, (I i).Internal) (hD : 0 < D)
    (f : UnitBall E → UnitBall E) (T : BasicPartition) (i : Fin D)
    (hparent : T.Respects (I i))
    (hchild : ∀ j, T.Respects ((I i).comp (I j))) :
    partitionColor I hI hD f (T.restrict (I i) hparent) =
      f (ballMean hD (fun j => partitionColor I hI hD f
        (T.restrict ((I i).comp (I j)) (hchild j)))) := by
  let hr : ∀ j, (T.restrict (I i) hparent).Respects (I j) :=
    fun j => T.restrict_respects (I i) (I j) hparent (hchild j)
  calc
    partitionColor I hI hD f (T.restrict (I i) hparent) =
        f (ballMean hD (fun j => partitionColor I hI hD f
          ((T.restrict (I i) hparent).restrict (I j) (hr j)))) :=
      partitionColor_of_respects I hI hD f _ hr
    _ = _ := by
      apply congrArg f
      apply congrArg (ballMean hD)
      funext j
      apply congrArg (partitionColor I hI hD f)
      exact T.restrict_restrict (I i) (I j) hparent (hchild j)

end ThompsonNonamenability

end

end OAI

end
end

section
section
namespace OAI

/-!
# A concrete finite family of separated internal dyadic intervals

At depth 2D use the cells with indices 2i+1. The bound 2D < 2^(2D)
leaves room at the right endpoint. Each adjacent selected pair has a positive
gap. The finite occurrence type remembers parents and their children without
requiring an injectivity premise for the family.
-/

noncomputable section

namespace ThompsonNonamenability

/-- The actual ith selected dyadic cell at common depth 2D. -/
def selectedInterval (D : ℕ) (i : Fin D) : BasicInterval where
  depth := 2 * D
  index := ⟨2 * i.val + 1, by
    have hi := i.isLt
    have hsmall : 2 * i.val + 1 < 2 * D := by omega
    exact hsmall.trans (2 * D).lt_two_pow_self⟩

theorem selectedInterval_internal (D : ℕ) (i : Fin D) :
    (selectedInterval D i).Internal := by
  have hp : (0 : ℝ) < (2 : ℝ) ^ (2 * D) := pow_pos (by norm_num) _
  constructor
  · change (0 : ℝ) < ((2 * i.val + 1 : ℕ) : ℝ) / (2 : ℝ) ^ (2 * D)
    exact div_pos (Nat.cast_pos.mpr (by omega)) hp
  · change (((2 * i.val + 1 : ℕ) : ℝ) + 1) / (2 : ℝ) ^ (2 * D) < 1
    apply (div_lt_one hp).2
    have hi := i.isLt
    have hsmall : 2 * i.val + 1 + 1 ≤ 2 * D := by omega
    have hlarge : 2 * i.val + 1 + 1 < 2 ^ (2 * D) :=
      hsmall.trans_lt (2 * D).lt_two_pow_self
    exact_mod_cast hlarge

theorem selectedInterval_before {D : ℕ} {i j : Fin D} (hij : i < j) :
    (selectedInterval D i).Before (selectedInterval D j) := by
  change (((2 * i.val + 1 : ℕ) : ℝ) + 1) / (2 : ℝ) ^ (2 * D) <
    ((2 * j.val + 1 : ℕ) : ℝ) / (2 : ℝ) ^ (2 * D)
  apply (div_lt_div_iff_of_pos_right (pow_pos (by norm_num : (0 : ℝ) < 2) _)).2
  have hv : i.val < j.val := hij
  have hn : 2 * i.val + 1 + 1 < 2 * j.val + 1 := by omega
  exact_mod_cast hn

/-- Strict separation permits either orientation and always has a positive gap. -/
def StrictlySeparated (I J : BasicInterval) : Prop := I.Before J ∨ J.Before I

theorem selectedInterval_separated {D : ℕ} {i j : Fin D} (hij : i ≠ j) :
    StrictlySeparated (selectedInterval D i) (selectedInterval D j) := by
  rcases lt_or_gt_of_ne hij with h | h
  · exact Or.inl (selectedInterval_before h)
  · exact Or.inr (selectedInterval_before h)

theorem selected_siblings_separated {D : ℕ} (i : Fin D) {j k : Fin D}
    (hjk : j ≠ k) :
    StrictlySeparated ((selectedInterval D i).comp (selectedInterval D j))
      ((selectedInterval D i).comp (selectedInterval D k)) := by
  rcases selectedInterval_separated hjk with h | h
  · exact Or.inl ((selectedInterval D i).comp_before_comp h)
  · exact Or.inr ((selectedInterval D i).comp_before_comp h)

/-- A descendant is separated from every parent except its own parent. -/
theorem selected_child_parent_separated {D : ℕ} (i j k : Fin D) (hki : k ≠ i) :
    StrictlySeparated ((selectedInterval D i).comp (selectedInterval D j))
      (selectedInterval D k) := by
  have hc := (selectedInterval D i).comp_contained (selectedInterval D j)
  rcases selectedInterval_separated (Ne.symm hki) with h | h
  · exact Or.inl (lt_of_le_of_lt hc.2 h)
  · exact Or.inr (lt_of_lt_of_le h hc.1)

abbrev IntervalIndex (D : ℕ) := Fin D ⊕ (Fin D × Fin D)

/-- Actual parent and second-generation intervals indexed by their occurrences. -/
def familyInterval (D : ℕ) : IntervalIndex D → BasicInterval
  | .inl i => selectedInterval D i
  | .inr (i, j) => (selectedInterval D i).comp (selectedInterval D j)

theorem familyInterval_internal (D : ℕ) (q : IntervalIndex D) :
    (familyInterval D q).Internal := by
  rcases q with i | ⟨i, j⟩
  · exact selectedInterval_internal D i
  · exact (selectedInterval D i).comp_internal_of_internal_right
      (selectedInterval D j) (selectedInterval_internal D j)

/-- The actual finite interval set used by the single admissibility condition. -/
def intervalFamily (D : ℕ) : Finset BasicInterval :=
  Finset.univ.image (familyInterval D)

theorem familyInterval_mem (D : ℕ) (q : IntervalIndex D) :
    familyInterval D q ∈ intervalFamily D :=
  Finset.mem_image.mpr ⟨q, Finset.mem_univ q, rfl⟩

def firstIndex {D : ℕ} (hD : 2 ≤ D) : Fin D :=
  ⟨0, lt_of_lt_of_le (by decide : 0 < 2) hD⟩

def secondIndex {D : ℕ} (hD : 2 ≤ D) : Fin D :=
  ⟨1, lt_of_lt_of_le (by decide : 1 < 2) hD⟩

theorem reference_before {D : ℕ} (hD : 2 ≤ D) :
    (selectedInterval D (firstIndex hD)).Before
      (selectedInterval D (secondIndex hD)) :=
  selectedInterval_before (show firstIndex hD < secondIndex hD from by
    change (0 : ℕ) < 1
    decide)

end ThompsonNonamenability

end

end OAI

end
end

section
section
namespace OAI

/-!
# The actual finite family of colors, including zero outside admissibility

A basic partition is admissible when it respects every chosen parent and
child. Its family color is always defined and lies in the unit ball. The
option extension also assigns zero to a non-basic image; the group-level
construction will supply the actual partial image partition.
-/

noncomputable section


namespace ThompsonNonamenability

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {D : ℕ}

/-- One simultaneous condition for all actual parent and child intervals. -/
def PartitionAdmissible (D : ℕ) (T : BasicPartition) : Prop :=
  ∀ q : IntervalIndex D, T.Respects (familyInterval D q)

/-- The family color is zero whenever the actual partition is inadmissible. -/
def partitionFamilyColor (hD : 0 < D) (f : UnitBall E → UnitBall E)
    (T : BasicPartition) (q : IntervalIndex D) : UnitBall E := by
  classical
  exact if h : PartitionAdmissible D T then
    partitionColor (selectedInterval D) (selectedInterval_internal D) hD f
      (T.restrict (familyInterval D q) (h q))
  else unitBallZero E

theorem partitionFamilyColor_of_admissible (hD : 0 < D)
    (f : UnitBall E → UnitBall E) (T : BasicPartition)
    (h : PartitionAdmissible D T) (q : IntervalIndex D) :
    partitionFamilyColor hD f T q =
      partitionColor (selectedInterval D) (selectedInterval_internal D) hD f
        (T.restrict (familyInterval D q) (h q)) := by
  simp only [partitionFamilyColor, dif_pos h]

/-- A parent's color is the map applied to its actual child-color mean. -/
theorem partitionFamilyColor_parent (hD : 0 < D)
    (f : UnitBall E → UnitBall E) (T : BasicPartition)
    (h : PartitionAdmissible D T) (i : Fin D) :
    partitionFamilyColor hD f T (.inl i) =
      f (ballMean hD (fun j => partitionFamilyColor hD f T (.inr (i, j)))) := by
  simp only [partitionFamilyColor_of_admissible hD f T h, familyInterval]
  exact partitionColor_restrict (selectedInterval D) (selectedInterval_internal D)
    hD f T i (h (.inl i)) (fun j => h (.inr (i, j)))

/-- Total zero extension at a non-basic image as well as an inadmissible one. -/
def optionFamilyColor (hD : 0 < D) (f : UnitBall E → UnitBall E) :
    Option BasicPartition → IntervalIndex D → UnitBall E
  | none, _ => unitBallZero E
  | some T, q => partitionFamilyColor hD f T q

@[simp] theorem optionFamilyColor_none (hD : 0 < D)
    (f : UnitBall E → UnitBall E) (q : IntervalIndex D) :
    optionFamilyColor hD f none q = unitBallZero E := rfl

@[simp] theorem optionFamilyColor_some (hD : 0 < D)
    (f : UnitBall E → UnitBall E) (T : BasicPartition) (q : IntervalIndex D) :
    optionFamilyColor hD f (some T) q = partitionFamilyColor hD f T q := rfl

end ThompsonNonamenability

end

end OAI

end
end

section
section
namespace OAI

/-!
# Uniform dyadic partitions

The depth-`n` partition consists of all `2^n` basic intervals at that depth.
Coverage includes both endpoints of the unit interval.  Distinct cells have
disjoint open interiors; their closed carriers may share an endpoint.
-/

noncomputable section

namespace ThompsonNonamenability.BasicPartition

open Set

/-- The cell with index `k` in the depth-`n` uniform dyadic partition. -/
def uniformCell (n : ℕ) (k : Fin (2 ^ n)) : BasicInterval :=
  ⟨n, k⟩

@[simp] theorem uniformCell_depth (n : ℕ) (k : Fin (2 ^ n)) :
    (uniformCell n k).depth = n := rfl

@[simp] theorem uniformCell_index (n : ℕ) (k : Fin (2 ^ n)) :
    (uniformCell n k).index = k := rfl

theorem uniformCell_injective (n : ℕ) : Function.Injective (uniformCell n) := by
  intro i j h
  apply Fin.ext
  exact congrArg (fun I : BasicInterval => I.index.val) h

/-- All cells at depth `n`, with no repeated intervals. -/
def uniformCells (n : ℕ) : Finset BasicInterval :=
  Finset.univ.map ⟨uniformCell n, uniformCell_injective n⟩

theorem mem_uniformCells {n : ℕ} {I : BasicInterval} :
    I ∈ uniformCells n ↔ ∃ k : Fin (2 ^ n), uniformCell n k = I := by
  simp [uniformCells]

@[simp] theorem uniformCell_mem_uniformCells (n : ℕ) (k : Fin (2 ^ n)) :
    uniformCell n k ∈ uniformCells n :=
  mem_uniformCells.mpr ⟨k, rfl⟩

@[simp] theorem card_uniformCells (n : ℕ) : (uniformCells n).card = 2 ^ n := by
  simp [uniformCells]

/-- At a fixed depth, the interiors of distinct cells are disjoint. -/
theorem uniformCell_disjoint {n : ℕ} {i j : Fin (2 ^ n)} (hij : i ≠ j) :
    Disjoint (uniformCell n i).interior (uniformCell n j).interior := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  change (i.val : ℝ) / (2 : ℝ) ^ n < x ∧
    x < ((i.val : ℝ) + 1) / (2 : ℝ) ^ n at hx
  change (j.val : ℝ) / (2 : ℝ) ^ n < x ∧
    x < ((j.val : ℝ) + 1) / (2 : ℝ) ^ n at hy
  have hd : 0 < (2 : ℝ) ^ n := pow_pos (by norm_num) n
  have hval : i.val ≠ j.val := fun h => hij (Fin.ext h)
  rcases lt_or_gt_of_ne hval with hlt | hlt
  · have hstep : (i.val : ℝ) + 1 ≤ (j.val : ℝ) := by
      exact_mod_cast Nat.succ_le_of_lt hlt
    have hsep : ((i.val : ℝ) + 1) / (2 : ℝ) ^ n ≤
        (j.val : ℝ) / (2 : ℝ) ^ n :=
      (div_le_div_iff_of_pos_right hd).mpr hstep
    exact (not_lt_of_ge hsep) (lt_trans hy.1 hx.2)
  · have hstep : (j.val : ℝ) + 1 ≤ (i.val : ℝ) := by
      exact_mod_cast Nat.succ_le_of_lt hlt
    have hsep : ((j.val : ℝ) + 1) / (2 : ℝ) ^ n ≤
        (i.val : ℝ) / (2 : ℝ) ^ n :=
      (div_le_div_iff_of_pos_right hd).mpr hstep
    exact (not_lt_of_ge hsep) (lt_trans hx.1 hy.2)

/-- Every point of `[0,1]` lies in one of the closed depth-`n` cells. -/
theorem uniformCells_cover (n : ℕ) (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
    ∃ I ∈ uniformCells n, x ∈ I.carrier := by
  have hnat : 0 < (2 : ℕ) ^ n := pow_pos (by decide) n
  have hd : 0 < (2 : ℝ) ^ n := pow_pos (by norm_num) n
  by_cases hx1 : x = 1
  · subst x
    have hk : 2 ^ n - 1 < 2 ^ n := Nat.sub_lt hnat (by decide)
    let k : Fin (2 ^ n) := ⟨2 ^ n - 1, hk⟩
    refine ⟨uniformCell n k, uniformCell_mem_uniformCells n k, ?_⟩
    change ((2 ^ n - 1 : ℕ) : ℝ) / (2 : ℝ) ^ n ≤ 1 ∧
      1 ≤ (((2 ^ n - 1 : ℕ) : ℝ) + 1) / (2 : ℝ) ^ n
    have hsucc : (2 ^ n - 1 : ℕ) + 1 = 2 ^ n :=
      Nat.sub_add_cancel hnat
    have hcast : (((2 ^ n - 1 : ℕ) : ℝ) + 1) = (2 : ℝ) ^ n := by
      exact_mod_cast hsucc
    constructor
    · apply (div_le_iff₀ hd).mpr
      linarith
    · rw [hcast, div_self (ne_of_gt hd)]
  · have hlt : x < 1 := lt_of_le_of_ne hx.2 hx1
    have hxD : 0 ≤ x * (2 : ℝ) ^ n := mul_nonneg hx.1 hd.le
    have hbound : x * (2 : ℝ) ^ n < ((2 ^ n : ℕ) : ℝ) := by
      simpa using (mul_lt_mul_of_pos_right hlt hd)
    have hk : ⌊x * (2 : ℝ) ^ n⌋₊ < 2 ^ n :=
      (Nat.floor_lt hxD).mpr hbound
    let k : Fin (2 ^ n) := ⟨⌊x * (2 : ℝ) ^ n⌋₊, hk⟩
    refine ⟨uniformCell n k, uniformCell_mem_uniformCells n k, ?_⟩
    change (⌊x * (2 : ℝ) ^ n⌋₊ : ℝ) / (2 : ℝ) ^ n ≤ x ∧
      x ≤ ((⌊x * (2 : ℝ) ^ n⌋₊ : ℝ) + 1) / (2 : ℝ) ^ n
    constructor
    · exact (div_le_iff₀ hd).mpr (Nat.floor_le hxD)
    · exact (le_div_iff₀ hd).mpr (Nat.lt_floor_add_one _).le

/-- The genuine partition into all depth-`n` dyadic cells. -/
def uniform (n : ℕ) : BasicPartition where
  cells := uniformCells n
  cover := uniformCells_cover n
  disjoint := by
    intro I hI J hJ hIJ
    obtain ⟨i, rfl⟩ := mem_uniformCells.mp hI
    obtain ⟨j, rfl⟩ := mem_uniformCells.mp hJ
    apply uniformCell_disjoint
    intro hij
    exact hIJ (congrArg (uniformCell n) hij)

@[simp] theorem uniform_cells (n : ℕ) : (uniform n).cells = uniformCells n := rfl

@[simp] theorem uniform_cellCount (n : ℕ) : (uniform n).cellCount = 2 ^ n := by
  exact card_uniformCells n

@[simp] theorem uniformCell_length (n : ℕ) (k : Fin (2 ^ n)) :
    (uniformCell n k).length = ((2 : ℝ) ^ n)⁻¹ := rfl

end ThompsonNonamenability.BasicPartition

end

end OAI

end
end

section
section
namespace OAI

/-!
# Resolving a finite dyadic PL subdivision on a uniform grid

All original knots lie on a sufficiently fine dyadic grid. Such a knot
cannot lie strictly between consecutive grid points. The source piece
containing a cell's midpoint therefore contains the whole closed cell.
-/

noncomputable section

namespace ThompsonNonamenability

open BasicPartition

/-- A point on the closed depth-`n` dyadic grid, including both endpoints. -/
def uniformDyadicPoint (n : ℕ) (j : Fin (2 ^ n + 1)) : UnitInterval :=
  ⟨(j.val : ℝ) / (2 : ℝ) ^ n, by
    constructor
    · exact div_nonneg (Nat.cast_nonneg _) (le_of_lt (pow_pos (by norm_num) n))
    · apply (div_le_one (pow_pos (by norm_num : (0 : ℝ) < 2) n)).mpr
      exact_mod_cast Nat.le_of_lt_succ j.isLt⟩

@[simp] theorem coe_uniformDyadicPoint (n : ℕ) (j : Fin (2 ^ n + 1)) :
    (uniformDyadicPoint n j : ℝ) = (j.val : ℝ) / (2 : ℝ) ^ n := rfl

@[simp] theorem uniformDyadicPoint_castSucc_coe (n : ℕ) (k : Fin (2 ^ n)) :
    (uniformDyadicPoint n k.castSucc : ℝ) = (uniformCell n k).left := rfl

@[simp] theorem uniformDyadicPoint_succ_coe (n : ℕ) (k : Fin (2 ^ n)) :
    (uniformDyadicPoint n k.succ : ℝ) = (uniformCell n k).right := by
  change (((k.val + 1 : ℕ) : ℝ) / (2 : ℝ) ^ n) =
    ((k.val : ℝ) + 1) / (2 : ℝ) ^ n
  simp only [Nat.cast_add, Nat.cast_one]

@[simp] theorem uniformDyadicPoint_zero (n : ℕ) :
    uniformDyadicPoint n 0 = unitIntervalZero := by
  apply Subtype.ext
  simp

@[simp] theorem uniformDyadicPoint_last (n : ℕ) :
    uniformDyadicPoint n (Fin.last (2 ^ n)) = unitIntervalOne := by
  apply Subtype.ext
  simp [Fin.val_last]

/-- There is no grid point strictly between consecutive grid points. -/
theorem grid_point_not_inside_uniform_cell (n : ℕ) (k : Fin (2 ^ n)) (j : ℤ) :
    ¬ ((uniformCell n k).left < (j : ℝ) / (2 : ℝ) ^ n ∧
      (j : ℝ) / (2 : ℝ) ^ n < (uniformCell n k).right) := by
  intro h
  have hd : (0 : ℝ) < (2 : ℝ) ^ n := pow_pos (by norm_num) n
  change (k.val : ℝ) / (2 : ℝ) ^ n < (j : ℝ) / (2 : ℝ) ^ n ∧
    (j : ℝ) / (2 : ℝ) ^ n < ((k.val : ℝ) + 1) / (2 : ℝ) ^ n at h
  have hleft : (k.val : ℤ) < j := by
    exact_mod_cast (div_lt_div_iff_of_pos_right hd).mp h.1
  have hright : j < (k.val : ℤ) + 1 := by
    exact_mod_cast (div_lt_div_iff_of_pos_right hd).mp h.2
  exact (not_lt_of_ge (Int.add_one_le_iff.mpr hleft)) hright

namespace DyadicPLWitness

/-- A single grid depth resolves every knot of the original subdivision.
At all larger depths each closed grid cell lies in one original piece. -/
theorem eventually_uniform_refines {f : IntervalHomeomorph} (w : DyadicPLWitness f) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ k : Fin (2 ^ n),
      ∃ i : Fin w.pieceCount,
        w.knots i.castSucc ≤ uniformDyadicPoint n k.castSucc ∧
        uniformDyadicPoint n k.succ ≤ w.knots i.succ := by
  classical
  obtain ⟨N, hN⟩ := dyadic_common_denominator_finset
    (Finset.univ : Finset (Fin (w.pieceCount + 1)))
    (fun j => (w.knots j : ℝ)) (fun j _ => w.dyadic j)
  refine ⟨N, ?_⟩
  intro n hn k
  let I := uniformCell n k
  have hlen : I.left < I.right := I.left_lt_right
  let m : UnitInterval := ⟨(I.left + I.right) / 2, by
    constructor <;> linarith [I.left_nonneg, I.right_le_one]⟩
  have hml : I.left < (m : ℝ) := by dsimp [m]; linarith
  have hmr : (m : ℝ) < I.right := by dsimp [m]; linarith
  obtain ⟨i, hil, hir⟩ := w.cover m
  have hilR : (w.knots i.castSucc : ℝ) ≤ (m : ℝ) := hil
  have hirR : (m : ℝ) ≤ (w.knots i.succ : ℝ) := hir
  have hno (j : Fin (w.pieceCount + 1)) :
      ¬ (I.left < (w.knots j : ℝ) ∧ (w.knots j : ℝ) < I.right) := by
    obtain ⟨a, ha⟩ := dyadic_denominator_mono (hN j (Finset.mem_univ j)) hn
    rw [ha]
    exact grid_point_not_inside_uniform_cell n k a
  refine ⟨i, ?_, ?_⟩
  · change (w.knots i.castSucc : ℝ) ≤ (uniformDyadicPoint n k.castSucc : ℝ)
    rw [uniformDyadicPoint_castSucc_coe]
    change (w.knots i.castSucc : ℝ) ≤ I.left
    apply le_of_not_gt
    intro h
    exact hno i.castSucc ⟨h, lt_of_le_of_lt hilR hmr⟩
  · change (uniformDyadicPoint n k.succ : ℝ) ≤ (w.knots i.succ : ℝ)
    rw [uniformDyadicPoint_succ_coe]
    change I.right ≤ (w.knots i.succ : ℝ)
    apply le_of_not_gt
    intro h
    exact hno i.succ ⟨lt_of_lt_of_le hml hirR, h⟩

end DyadicPLWitness

namespace DyadicPLWitness

end DyadicPLWitness

namespace UniformDyadicPLWitness

end UniformDyadicPLWitness

end ThompsonNonamenability

end

end OAI

end
end

section
section
namespace OAI

/-!
# Alignment of dyadic affine images with basic intervals

A slope which is an integer power of two sends every sufficiently fine grid
cell to a single grid cell, provided its dyadic translation has been absorbed
into the target denominator. The target depth can be made arbitrarily large.
-/

namespace ThompsonNonamenability

/-- An integer grid cell lying in the unit interval is a basic interval. -/
theorem basicInterval_of_integer_grid (d : ℕ) (j : ℤ)
    (h0 : 0 ≤ (j : ℝ) / (2 : ℝ) ^ d)
    (h1 : ((j : ℝ) + 1) / (2 : ℝ) ^ d ≤ 1) :
    ∃ I : BasicInterval, I.depth = d ∧
      I.left = (j : ℝ) / (2 : ℝ) ^ d ∧
      I.right = ((j : ℝ) + 1) / (2 : ℝ) ^ d := by
  have hp : (0 : ℝ) < (2 : ℝ) ^ d := pow_pos (by norm_num) _
  have hjr : (0 : ℝ) ≤ (j : ℝ) := by
    have hh := (le_div_iff₀ hp).1 h0
    simpa only [zero_mul] using hh
  have hj : (0 : ℤ) ≤ j := by exact_mod_cast hjr
  have hc : (j.toNat : ℝ) = (j : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg hj
  have hbound : j.toNat < 2 ^ d := by
    have hh : (j.toNat : ℝ) + 1 ≤ (2 : ℝ) ^ d := by
      rw [hc]
      exact (div_le_one hp).1 h1
    have hn : j.toNat + 1 ≤ 2 ^ d := by exact_mod_cast hh
    omega
  refine ⟨⟨d, ⟨j.toNat, hbound⟩⟩, rfl, ?_, ?_⟩
  · change (j.toNat : ℝ) / (2 : ℝ) ^ d = _
    rw [hc]
  · change ((j.toNat : ℝ) + 1) / (2 : ℝ) ^ d = _
    rw [hc]

/-- The target denominator simultaneously absorbs the translation and slope.
The freely specified lower bound on target depth gives arbitrarily small cells. -/
theorem dyadic_affine_aligned_denominators (q : ℤ) (b : ℝ)
    (hb : IsDyadic b) (L : ℕ) :
    ∃ N : ℕ, ∀ n ≥ N, ∃ d : ℕ, L ≤ d ∧
      (∃ j : ℤ, b = (j : ℝ) / (2 : ℝ) ^ d) ∧
      (2 : ℝ) ^ q / (2 : ℝ) ^ n = 1 / (2 : ℝ) ^ d := by
  obtain ⟨j, m, hj⟩ := hb
  cases q with
  | ofNat p =>
      refine ⟨m + L + p, ?_⟩
      intro n hn
      obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hn
      refine ⟨m + L + t, by omega, ?_, ?_⟩
      · exact dyadic_denominator_mono ⟨j, hj⟩ (by omega)
      · rw [Int.ofNat_eq_natCast, zpow_natCast]
        have he : m + L + p + t = p + (m + L + t) := by omega
        rw [he, pow_add]
        field_simp
  | negSucc p =>
      refine ⟨m + L, ?_⟩
      intro n hn
      obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hn
      refine ⟨m + L + t + (p + 1), by omega, ?_, ?_⟩
      · exact dyadic_denominator_mono ⟨j, hj⟩ (by omega)
      · rw [zpow_negSucc, pow_add]
        field_simp ; ring

/-- A single cell is aligned when the slope and translation share the target
grid denominator. No assumption about the source cell's location is needed. -/
theorem dyadic_affine_cell_of_denominator (q : ℤ) (b : ℝ) (n d : ℕ)
    (hb : ∃ j : ℤ, b = (j : ℝ) / (2 : ℝ) ^ d)
    (hs : (2 : ℝ) ^ q / (2 : ℝ) ^ n = 1 / (2 : ℝ) ^ d)
    (k : Fin (2 ^ n))
    (h0 : 0 ≤ (2 : ℝ) ^ q * ((k.val : ℝ) / (2 : ℝ) ^ n) + b)
    (h1 : (2 : ℝ) ^ q * (((k.val : ℝ) + 1) / (2 : ℝ) ^ n) + b ≤ 1) :
    ∃ I : BasicInterval, I.depth = d ∧
      I.left = (2 : ℝ) ^ q * ((k.val : ℝ) / (2 : ℝ) ^ n) + b ∧
      I.right = (2 : ℝ) ^ q * (((k.val : ℝ) + 1) / (2 : ℝ) ^ n) + b := by
  obtain ⟨j, hj⟩ := hb
  have hl : (2 : ℝ) ^ q * ((k.val : ℝ) / (2 : ℝ) ^ n) + b =
      (((k.val : ℤ) + j : ℤ) : ℝ) / (2 : ℝ) ^ d := by
    calc
      _ = ((2 : ℝ) ^ q / (2 : ℝ) ^ n) * (k.val : ℝ) + b := by ring
      _ = (1 / (2 : ℝ) ^ d) * (k.val : ℝ) + (j : ℝ) / (2 : ℝ) ^ d := by
        rw [hs, hj]
      _ = _ := by push_cast; ring
  have hr : (2 : ℝ) ^ q * (((k.val : ℝ) + 1) / (2 : ℝ) ^ n) + b =
      ((((k.val : ℤ) + j : ℤ) : ℝ) + 1) / (2 : ℝ) ^ d := by
    calc
      _ = ((2 : ℝ) ^ q / (2 : ℝ) ^ n) * ((k.val : ℝ) + 1) + b := by ring
      _ = (1 / (2 : ℝ) ^ d) * ((k.val : ℝ) + 1) + (j : ℝ) / (2 : ℝ) ^ d := by
        rw [hs, hj]
      _ = _ := by push_cast; ring
  obtain ⟨I, hd, hleft, hright⟩ := basicInterval_of_integer_grid d ((k.val : ℤ) + j)
    (hl ▸ h0) (hr ▸ h1)
  exact ⟨I, hd, hleft.trans hl.symm, hright.trans hr.symm⟩

/-- The affine image cells can simultaneously be required to have any prescribed
positive upper bound on their length. -/
theorem dyadic_affine_grid_alignment_small (q : ℤ) (b : ℝ) (hb : IsDyadic b)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ k : Fin (2 ^ n),
      0 ≤ (2 : ℝ) ^ q * ((k.val : ℝ) / (2 : ℝ) ^ n) + b →
      (2 : ℝ) ^ q * (((k.val : ℝ) + 1) / (2 : ℝ) ^ n) + b ≤ 1 →
      ∃ I : BasicInterval,
        I.left = (2 : ℝ) ^ q * ((k.val : ℝ) / (2 : ℝ) ^ n) + b ∧
        I.right = (2 : ℝ) ^ q * (((k.val : ℝ) + 1) / (2 : ℝ) ^ n) + b ∧
        I.length < ε := by
  obtain ⟨L, hL⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (2 : ℝ)⁻¹ < 1)
  have hL' : 1 / (2 : ℝ) ^ L < ε := by
    simpa only [inv_pow, one_div] using hL
  obtain ⟨N, hN⟩ := dyadic_affine_aligned_denominators q b hb L
  refine ⟨N, ?_⟩
  intro n hn k h0 h1
  obtain ⟨d, hd, hb', hs⟩ := hN n hn
  obtain ⟨I, hdepth, hl, hr⟩ := dyadic_affine_cell_of_denominator q b n d hb' hs k h0 h1
  refine ⟨I, hl, hr, ?_⟩
  have hpow : (2 : ℝ) ^ L ≤ (2 : ℝ) ^ d :=
    pow_le_pow_right₀ (by norm_num) hd
  have hle := one_div_le_one_div_of_le (pow_pos (by norm_num : (0 : ℝ) < 2) L) hpow
  change ((2 : ℝ) ^ I.depth)⁻¹ < ε
  rw [hdepth, ← one_div]
  exact hle.trans_lt hL'

end ThompsonNonamenability

end OAI

end
end

section
section
namespace OAI

noncomputable section

namespace ThompsonNonamenability

open BasicPartition

/-- Every actual image of a depth-`n` uniform cell is a basic interval. -/
def ImageBasic (g : F) (n : ℕ) : Prop :=
  ∀ k : Fin (2 ^ n), ∃ I : BasicInterval,
    I.left = (g (uniformDyadicPoint n k.castSucc) : ℝ) ∧
    I.right = (g (uniformDyadicPoint n k.succ) : ℝ)

/-- The unique basic interval with the actual image endpoints. -/
def imageCell (g : F) (n : ℕ) (hg : ImageBasic g n) (k : Fin (2 ^ n)) :
    BasicInterval := Classical.choose (hg k)

@[simp] theorem imageCell_left (g : F) (n : ℕ) (hg : ImageBasic g n)
    (k : Fin (2 ^ n)) :
    (imageCell g n hg k).left = (g (uniformDyadicPoint n k.castSucc) : ℝ) :=
  (Classical.choose_spec (hg k)).1

@[simp] theorem imageCell_right (g : F) (n : ℕ) (hg : ImageBasic g n)
    (k : Fin (2 ^ n)) :
    (imageCell g n hg k).right = (g (uniformDyadicPoint n k.succ) : ℝ) :=
  (Classical.choose_spec (hg k)).2

theorem imageCell_mem_carrier_iff (g : F) (n : ℕ) (hg : ImageBasic g n)
    (k : Fin (2 ^ n)) (x : UnitInterval) :
    (g x : ℝ) ∈ (imageCell g n hg k).carrier ↔
      (x : ℝ) ∈ (uniformCell n k).carrier := by
  simp only [BasicInterval.carrier, Set.mem_Icc, imageCell_left, imageCell_right]
  change g (uniformDyadicPoint n k.castSucc) ≤ g x ∧
      g x ≤ g (uniformDyadicPoint n k.succ) ↔ _
  rw [g.strictMono.le_iff_le, g.strictMono.le_iff_le]
  change (uniformDyadicPoint n k.castSucc : ℝ) ≤ (x : ℝ) ∧
      (x : ℝ) ≤ (uniformDyadicPoint n k.succ : ℝ) ↔ _
  rw [uniformDyadicPoint_castSucc_coe, uniformDyadicPoint_succ_coe]

theorem imageCell_mem_interior_iff (g : F) (n : ℕ) (hg : ImageBasic g n)
    (k : Fin (2 ^ n)) (x : UnitInterval) :
    (g x : ℝ) ∈ (imageCell g n hg k).interior ↔
      (x : ℝ) ∈ (uniformCell n k).interior := by
  simp only [BasicInterval.interior, Set.mem_Ioo, imageCell_left, imageCell_right]
  change g (uniformDyadicPoint n k.castSucc) < g x ∧
      g x < g (uniformDyadicPoint n k.succ) ↔ _
  rw [g.strictMono.lt_iff_lt, g.strictMono.lt_iff_lt]
  change (uniformDyadicPoint n k.castSucc : ℝ) < (x : ℝ) ∧
      (x : ℝ) < (uniformDyadicPoint n k.succ : ℝ) ↔ _
  rw [uniformDyadicPoint_castSucc_coe, uniformDyadicPoint_succ_coe]

theorem imageCell_injective (g : F) (n : ℕ) (hg : ImageBasic g n) :
    Function.Injective (imageCell g n hg) := by
  intro k l heq
  have hl : (g (uniformDyadicPoint n k.castSucc) : ℝ) =
      (g (uniformDyadicPoint n l.castSucc) : ℝ) := by
    simpa only [imageCell_left] using congrArg BasicInterval.left heq
  have hp := g.strictMono.injective (Subtype.ext hl)
  have hp' := congrArg (fun x : UnitInterval => (x : ℝ)) hp
  have hd : (2 : ℝ) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
  change (k.val : ℝ) / (2 : ℝ) ^ n = (l.val : ℝ) / (2 : ℝ) ^ n at hp'
  have hk : (k.val : ℝ) = (l.val : ℝ) := (div_left_inj' hd).mp hp'
  apply Fin.ext
  exact_mod_cast hk

/-- The actual images, with coverage and disjoint open interiors proved. -/
def imagePartition (g : F) (n : ℕ) (hg : ImageBasic g n) : BasicPartition where
  cells := Finset.univ.image (imageCell g n hg)
  cover := by
    intro x hx
    let y : UnitInterval := g.toHomeomorph.symm ⟨x, hx⟩
    have hgy : g y = (⟨x, hx⟩ : UnitInterval) :=
      g.toHomeomorph.apply_symm_apply ⟨x, hx⟩
    obtain ⟨I, hI, hyI⟩ := uniformCells_cover n (y : ℝ) y.property
    obtain ⟨k, rfl⟩ := mem_uniformCells.mp hI
    refine ⟨imageCell g n hg k, Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩, ?_⟩
    have hm := (imageCell_mem_carrier_iff g n hg k y).mpr hyI
    simpa only [hgy] using hm
  disjoint := by
    intro I hI J hJ hne
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hI
    obtain ⟨l, _, rfl⟩ := Finset.mem_image.mp hJ
    apply Set.disjoint_left.mpr
    intro x hxk hxl
    have hx : x ∈ Set.Icc (0 : ℝ) 1 :=
      (imageCell g n hg k).carrier_subset_unit
        ((imageCell g n hg k).interior_subset_carrier hxk)
    let y : UnitInterval := g.toHomeomorph.symm ⟨x, hx⟩
    have hgy : g y = (⟨x, hx⟩ : UnitInterval) :=
      g.toHomeomorph.apply_symm_apply ⟨x, hx⟩
    have hyk : (y : ℝ) ∈ (uniformCell n k).interior :=
      (imageCell_mem_interior_iff g n hg k y).mp (by simpa only [hgy] using hxk)
    have hyl : (y : ℝ) ∈ (uniformCell n l).interior :=
      (imageCell_mem_interior_iff g n hg l y).mp (by simpa only [hgy] using hxl)
    have hkl : k ≠ l := fun h => hne (congrArg (imageCell g n hg) h)
    exact Set.disjoint_left.mp (uniformCell_disjoint hkl) hyk hyl

@[simp] theorem imagePartition_cells (g : F) (n : ℕ) (hg : ImageBasic g n) :
    (imagePartition g n hg).cells = Finset.univ.image (imageCell g n hg) := rfl

@[simp] theorem mem_imagePartition_cells (g : F) (n : ℕ) (hg : ImageBasic g n)
    (I : BasicInterval) :
    I ∈ (imagePartition g n hg).cells ↔ ∃ k, imageCell g n hg k = I := by
  simp only [imagePartition_cells, Finset.mem_image, Finset.mem_univ, true_and]

@[simp] theorem imagePartition_cellCount (g : F) (n : ℕ) (hg : ImageBasic g n) :
    (imagePartition g n hg).cellCount = 2 ^ n := by
  simp only [BasicPartition.cellCount, imagePartition_cells,
    Finset.card_image_of_injective _ (imageCell_injective g n hg), Finset.card_univ,
    Fintype.card_fin]

/-- Simultaneously gives actual image cells and the desired mesh bound. -/
theorem eventually_image_cells_small (g : F) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ k : Fin (2 ^ n), ∃ I : BasicInterval,
      I.left = (g (uniformDyadicPoint n k.castSucc) : ℝ) ∧
      I.right = (g (uniformDyadicPoint n k.succ) : ℝ) ∧ I.length < ε := by
  let w := g.witness
  let b : Fin w.pieceCount → ℝ := fun i =>
    (g (w.knots i.castSucc) : ℝ) -
      (2 : ℝ) ^ w.exponent i * (w.knots i.castSucc : ℝ)
  have hb : ∀ i, IsDyadic (b i) := by
    intro i
    exact (w.image_knots_dyadic g.strictMono i.castSucc).sub
      ((isDyadic_zpow (w.exponent i)).mul (w.dyadic i.castSucc))
  have halign := fun i => dyadic_affine_grid_alignment_small
    (w.exponent i) (b i) (hb i) ε hε
  choose Ns hNs using halign
  obtain ⟨Nr, hNr⟩ := w.eventually_uniform_refines
  refine ⟨max Nr (Finset.univ.sup Ns), ?_⟩
  intro n hn k
  obtain ⟨i, hil, hir⟩ := hNr n ((le_max_left _ _).trans hn) k
  have horder : uniformDyadicPoint n k.castSucc ≤ uniformDyadicPoint n k.succ := by
    change (uniformDyadicPoint n k.castSucc : ℝ) ≤ (uniformDyadicPoint n k.succ : ℝ)
    rw [uniformDyadicPoint_castSucc_coe, uniformDyadicPoint_succ_coe]
    exact (uniformCell n k).left_lt_right.le
  have hl := w.affine i (uniformDyadicPoint n k.castSucc) hil (horder.trans hir)
  have hr := w.affine i (uniformDyadicPoint n k.succ) (hil.trans horder) hir
  have hleft : (g (uniformDyadicPoint n k.castSucc) : ℝ) =
      (2 : ℝ) ^ w.exponent i * ((k.val : ℝ) / (2 : ℝ) ^ n) + b i := by
    change (g (uniformDyadicPoint n k.castSucc) : ℝ) = _ at hl
    rw [uniformDyadicPoint_castSucc_coe] at hl
    change (g (uniformDyadicPoint n k.castSucc) : ℝ) =
      (g (w.knots i.castSucc) : ℝ) +
        (2 : ℝ) ^ w.exponent i * ((k.val : ℝ) / (2 : ℝ) ^ n - _) at hl
    dsimp only [b]
    nlinarith [hl]
  have hright : (g (uniformDyadicPoint n k.succ) : ℝ) =
      (2 : ℝ) ^ w.exponent i * (((k.val : ℝ) + 1) / (2 : ℝ) ^ n) + b i := by
    change (g (uniformDyadicPoint n k.succ) : ℝ) = _ at hr
    rw [uniformDyadicPoint_succ_coe] at hr
    change (g (uniformDyadicPoint n k.succ) : ℝ) =
      (g (w.knots i.castSucc) : ℝ) +
        (2 : ℝ) ^ w.exponent i * (((k.val : ℝ) + 1) / (2 : ℝ) ^ n - _) at hr
    dsimp only [b]
    nlinarith [hr]
  have hNi : Ns i ≤ n :=
    (Finset.le_sup (Finset.mem_univ i)).trans ((le_max_right _ _).trans hn)
  obtain ⟨I, hIl, hIr, hIs⟩ := hNs i n hNi k
    (hleft ▸ (g (uniformDyadicPoint n k.castSucc)).property.1)
    (hright ▸ (g (uniformDyadicPoint n k.succ)).property.2)
  exact ⟨I, hIl.trans hleft.symm, hIr.trans hright.symm, hIs⟩

theorem eventually_image_basic (g : F) : ∃ N, ∀ n ≥ N, ImageBasic g n := by
  obtain ⟨N, hN⟩ := eventually_image_cells_small g 1 zero_lt_one
  refine ⟨N, ?_⟩
  intro n hn k
  obtain ⟨I, hl, hr, _⟩ := hN n hn k
  exact ⟨I, hl, hr⟩

theorem eventually_image_mesh_lt (g : F) (ε : ℝ) (hε : 0 < ε) :
    ∃ N, ∀ n ≥ N, ∃ hg : ImageBasic g n,
      ∀ I ∈ (imagePartition g n hg).cells, I.length < ε := by
  obtain ⟨N, hN⟩ := eventually_image_cells_small g ε hε
  refine ⟨N, ?_⟩
  intro n hn
  have hg : ImageBasic g n := by
    intro k
    obtain ⟨I, hl, hr, _⟩ := hN n hn k
    exact ⟨I, hl, hr⟩
  refine ⟨hg, ?_⟩
  intro I hI
  obtain ⟨k, rfl⟩ := (mem_imagePartition_cells g n hg I).mp hI
  obtain ⟨J, hl, hr, hJ⟩ := hN n hn k
  have heq : imageCell g n hg k = J :=
    BasicInterval.ext_endpoints ((imageCell_left g n hg k).trans hl.symm)
      ((imageCell_right g n hg k).trans hr.symm)
  simpa only [heq] using hJ

/-- A single actual grid level works for both finite families. -/
theorem eventually_image_respects (K : Finset F) (J : Finset BasicInterval) :
    ∃ N, ∀ n ≥ N, ∀ g ∈ K, ∃ hg : ImageBasic g n,
      ∀ I ∈ J, (imagePartition g n hg).Respects I := by
  classical
  have hsingle : ∀ g : F, ∃ N, ∀ n ≥ N, ∃ hg : ImageBasic g n,
      ∀ I ∈ J, (imagePartition g n hg).Respects I := by
    intro g
    induction J using Finset.induction_on with
    | empty =>
        obtain ⟨N, hN⟩ := eventually_image_basic g
        exact ⟨N, fun n hn => ⟨hN n hn, by simp⟩⟩
    | @insert I J hIJ ih =>
        obtain ⟨N₁, hN₁⟩ := ih
        obtain ⟨N₂, hN₂⟩ := eventually_image_mesh_lt g I.length I.length_pos
        refine ⟨max N₁ N₂, ?_⟩
        intro n hn
        obtain ⟨hg, hrest⟩ := hN₁ n ((le_max_left _ _).trans hn)
        obtain ⟨hg', hmesh⟩ := hN₂ n ((le_max_right _ _).trans hn)
        refine ⟨hg, ?_⟩
        intro L hL
        rcases Finset.mem_insert.mp hL with hLI | hL
        · subst L
          exact (imagePartition g n hg).respects_of_mesh_lt I hmesh
        · exact hrest L hL
  choose Ns hNs using hsingle
  refine ⟨K.sup Ns, ?_⟩
  intro n hn g hg
  exact hNs g n ((Finset.le_sup hg).trans hn)

end ThompsonNonamenability

end

end OAI

end
end

section
section
namespace OAI

/-!
# Actual affine charts of basic intervals

The chart is bundled as a point of the real unit interval. Affine transport
means equality of these actual maps at every point, including both endpoints.
-/

noncomputable section

namespace ThompsonNonamenability

namespace BasicInterval

def chartPoint (I : BasicInterval) (x : UnitInterval) : UnitInterval :=
  ⟨I.chart (x : ℝ), I.carrier_subset_unit
    ((I.chart_mem_self_carrier_iff (x : ℝ)).mpr x.property)⟩

@[simp] theorem coe_chartPoint (I : BasicInterval) (x : UnitInterval) :
    (I.chartPoint x : ℝ) = I.chart (x : ℝ) := rfl

@[simp] theorem chartPoint_comp (I J : BasicInterval) (x : UnitInterval) :
    (I.comp J).chartPoint x = I.chartPoint (J.chartPoint x) := by
  apply Subtype.ext
  exact I.chart_comp J (x : ℝ)

theorem chartPoint_mem_carrier (I : BasicInterval) (x : UnitInterval) :
    (I.chartPoint x : ℝ) ∈ I.carrier :=
  (I.chart_mem_self_carrier_iff (x : ℝ)).mpr x.property

theorem left_isDyadic (I : BasicInterval) : IsDyadic I.left := by
  exact ⟨(I.index.val : ℤ), I.depth, by simp only [left, Int.cast_natCast]⟩

theorem right_isDyadic (I : BasicInterval) : IsDyadic I.right := by
  exact ⟨(I.index.val : ℤ) + 1, I.depth, by
    simp only [right, Int.cast_add, Int.cast_natCast, Int.cast_one]⟩

end BasicInterval

def CarriesAffinely (h : F) (I J : BasicInterval) : Prop :=
  ∀ x : UnitInterval, (h (I.chartPoint x) : ℝ) = J.chart (x : ℝ)

namespace CarriesAffinely

theorem comp {h : F} {I J : BasicInterval} (hc : CarriesAffinely h I J)
    (K : BasicInterval) : CarriesAffinely h (I.comp K) (J.comp K) := by
  intro x
  simpa only [BasicInterval.chartPoint_comp, BasicInterval.chart_comp,
    BasicInterval.coe_chartPoint] using hc (K.chartPoint x)

end CarriesAffinely

end ThompsonNonamenability

end

end OAI

end
end

section
section
namespace OAI

/-!
# Exact covariance under actual affine transport

Every source image cell and its target image cell retain the same original
uniform-grid index. The affine chart equality therefore identifies the
normalized restrictions pointwise, including their closed endpoints.
-/

namespace ThompsonNonamenability

namespace CarriesAffinely

theorem chart_value_eq_iff {h : F} {I J : BasicInterval}
    (hc : CarriesAffinely h I J) (x y : UnitInterval) :
    (h x : ℝ) = J.chart (y : ℝ) ↔ (x : ℝ) = I.chart (y : ℝ) := by
  constructor
  · intro hx
    have heq : h x = h (I.chartPoint y) :=
      Subtype.ext (hx.trans (hc y).symm)
    exact congrArg (fun z : UnitInterval => (z : ℝ)) (h.strictMono.injective heq)
  · intro hx
    have heq : x = I.chartPoint y := Subtype.ext hx
    rw [heq]
    exact hc y

theorem left_value_eq_iff {h : F} {I J : BasicInterval}
    (hc : CarriesAffinely h I J) (x : UnitInterval) :
    (h x : ℝ) = J.left ↔ (x : ℝ) = I.left := by
  simpa only [coe_unitIntervalZero, BasicInterval.chart_zero] using
    hc.chart_value_eq_iff x unitIntervalZero

theorem right_value_eq_iff {h : F} {I J : BasicInterval}
    (hc : CarriesAffinely h I J) (x : UnitInterval) :
    (h x : ℝ) = J.right ↔ (x : ℝ) = I.right := by
  simpa only [coe_unitIntervalOne, BasicInterval.chart_one] using
    hc.chart_value_eq_iff x unitIntervalOne

end CarriesAffinely

/-- Corresponding actual image cells have exactly the affinely transported
endpoints. No admissibility of any other interval is assumed here. -/
theorem imageCell_transport_iff (h g : F) (n : ℕ)
    (I I' : BasicInterval) (hc : CarriesAffinely h I I')
    (hg : ImageBasic g n) (hhg : ImageBasic (h * g) n) (k : Fin (2 ^ n)) :
    imageCell (h * g) n hhg k = I' ↔ imageCell g n hg k = I := by
  constructor
  · intro heq
    apply BasicInterval.ext_endpoints
    · have hl := congrArg BasicInterval.left heq
      simp only [imageCell_left, F.mul_apply] at hl
      rw [imageCell_left]
      exact (hc.left_value_eq_iff _).mp hl
    · have hr := congrArg BasicInterval.right heq
      simp only [imageCell_right, F.mul_apply] at hr
      rw [imageCell_right]
      exact (hc.right_value_eq_iff _).mp hr
  · intro heq
    apply BasicInterval.ext_endpoints
    · have hl := congrArg BasicInterval.left heq
      simp only [imageCell_left] at hl
      rw [imageCell_left, F.mul_apply]
      exact (hc.left_value_eq_iff _).mpr hl
    · have hr := congrArg BasicInterval.right heq
      simp only [imageCell_right] at hr
      rw [imageCell_right, F.mul_apply]
      exact (hc.right_value_eq_iff _).mpr hr

/-- Exact normalized restriction covariance for multiplication `h * g = h ∘ g`. -/
theorem image_restrict_covariance
    (h g : F) (n : ℕ) (I I' : BasicInterval)
    (hc : CarriesAffinely h I I')
    (hg : ImageBasic g n) (hhg : ImageBasic (h * g) n)
    (hr : (imagePartition g n hg).Respects I)
    (hr' : (imagePartition (h * g) n hhg).Respects I') :
    (imagePartition (h * g) n hhg).restrict I' hr' =
      (imagePartition g n hg).restrict I hr := by
  apply BasicPartition.ext
  ext K
  simp only [BasicPartition.mem_restrict_cells, mem_imagePartition_cells]
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k, (imageCell_transport_iff h g n (I.comp K) (I'.comp K)
      (hc.comp K) hg hhg k).mp hk⟩
  · rintro ⟨k, hk⟩
    exact ⟨k, (imageCell_transport_iff h g n (I.comp K) (I'.comp K)
      (hc.comp K) hg hhg k).mpr hk⟩

end ThompsonNonamenability

end OAI

end
end

section
section
namespace OAI

/-!
# Real finite averages and left-translation cancellation

These are literal finite sums. The translation estimate cancels the common
intersection of the two finite sets, and the function bound is global. No
invariant mean, support assumption, or limiting average is used.
-/

noncomputable section


namespace ThompsonNonamenability

open scoped BigOperators symmDiff

variable {α : Type uα} {ι : Type uι}

def realAvg (A : Finset α) (f : α → ℝ) : ℝ :=
  (A.card : ℝ)⁻¹ * ∑ x ∈ A, f x

theorem realAvg_eq_sum_div (A : Finset α) (f : α → ℝ) :
    realAvg A f = (∑ x ∈ A, f x) / (A.card : ℝ) := by
  simp only [realAvg, div_eq_mul_inv, mul_comm]

theorem realAvg_congr (A : Finset α) {f g : α → ℝ}
    (hfg : ∀ x ∈ A, f x = g x) : realAvg A f = realAvg A g := by
  unfold realAvg
  rw [Finset.sum_congr rfl hfg]

@[simp] theorem realAvg_zero (A : Finset α) : realAvg A (fun _ => 0) = 0 := by
  simp [realAvg]

theorem realAvg_add (A : Finset α) (f g : α → ℝ) :
    realAvg A (fun x => f x + g x) = realAvg A f + realAvg A g := by
  simp only [realAvg, Finset.sum_add_distrib, mul_add]

theorem realAvg_sub (A : Finset α) (f g : α → ℝ) :
    realAvg A (fun x => f x - g x) = realAvg A f - realAvg A g := by
  simp only [realAvg, Finset.sum_sub_distrib, mul_sub]

theorem realAvg_const_mul (A : Finset α) (c : ℝ) (f : α → ℝ) :
    realAvg A (fun x => c * f x) = c * realAvg A f := by
  simp only [realAvg, ← Finset.mul_sum, mul_left_comm]

theorem realAvg_sum (A : Finset α) (B : Finset ι) (f : ι → α → ℝ) :
    realAvg A (fun x => ∑ i ∈ B, f i x) = ∑ i ∈ B, realAvg A (f i) := by
  unfold realAvg
  rw [Finset.sum_comm, Finset.mul_sum]

theorem realAvg_sum_univ [Fintype ι] (A : Finset α) (f : ι → α → ℝ) :
    realAvg A (fun x => ∑ i, f i x) = ∑ i, realAvg A (f i) :=
  realAvg_sum A Finset.univ f

theorem realAvg_mono (A : Finset α) {f g : α → ℝ}
    (hfg : ∀ x ∈ A, f x ≤ g x) : realAvg A f ≤ realAvg A g :=
  mul_le_mul_of_nonneg_left (Finset.sum_le_sum hfg)
    (inv_nonneg.mpr (Nat.cast_nonneg A.card))

theorem realAvg_const (A : Finset α) (hA : A.Nonempty) (c : ℝ) :
    realAvg A (fun _ => c) = c := by
  have hc : (A.card : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr (Finset.card_pos.mpr hA))
  simp [realAvg, nsmul_eq_mul, hc]

theorem realAvg_le_const (A : Finset α) (hA : A.Nonempty) {f : α → ℝ} {c : ℝ}
    (hf : ∀ x ∈ A, f x ≤ c) : realAvg A f ≤ c := by
  simpa only [realAvg_const A hA c] using realAvg_mono A hf

theorem const_le_realAvg (A : Finset α) (hA : A.Nonempty) {f : α → ℝ} {c : ℝ}
    (hf : ∀ x ∈ A, c ≤ f x) : c ≤ realAvg A f := by
  simpa only [realAvg_const A hA c] using realAvg_mono A hf

section Cancellation

variable [DecidableEq α]

/-- The exact common-intersection cancellation, before any estimate. -/
theorem sum_sub_eq_sdiff_sub (U V : Finset α) (f : α → ℝ) :
    (∑ x ∈ U, f x) - ∑ x ∈ V, f x =
      (∑ x ∈ U \ V, f x) - ∑ x ∈ V \ U, f x :=
  (Finset.sum_sdiff_sub_sum_sdiff (s₁ := V) (s₂ := U) (f := f)).symm

theorem card_symmDiff_eq_sdiff_add (U V : Finset α) :
    (U ∆ V).card = (U \ V).card + (V \ U).card := by
  change ((U \ V) ∪ (V \ U)).card = _
  exact Finset.card_union_of_disjoint disjoint_sdiff_sdiff

omit [DecidableEq α] in
theorem abs_sum_le_card [DecidableEq α] (A : Finset α) (f : α → ℝ) (hf : ∀ x, |f x| ≤ 1) :
    |∑ x ∈ A, f x| ≤ (A.card : ℝ) := by
  calc
    |∑ x ∈ A, f x| ≤ ∑ x ∈ A, |f x| := Finset.abs_sum_le_sum_abs f A
    _ ≤ ∑ _x ∈ A, (1 : ℝ) := Finset.sum_le_sum (fun x _ => hf x)
    _ = (A.card : ℝ) := by simp

/-- The full symmetric difference counts both residual pieces exactly once. -/
theorem abs_sum_sub_le_card_symmDiff (U V : Finset α) (f : α → ℝ)
    (hf : ∀ x, |f x| ≤ 1) :
    |(∑ x ∈ U, f x) - ∑ x ∈ V, f x| ≤ ((U ∆ V).card : ℝ) := by
  rw [sum_sub_eq_sdiff_sub]
  calc
    |(∑ x ∈ U \ V, f x) - ∑ x ∈ V \ U, f x| ≤
        |∑ x ∈ U \ V, f x| + |∑ x ∈ V \ U, f x| := by
      simpa only [sub_eq_add_neg, abs_neg] using
        abs_add_le (∑ x ∈ U \ V, f x) (-(∑ x ∈ V \ U, f x))
    _ ≤ ((U \ V).card : ℝ) + ((V \ U).card : ℝ) :=
      add_le_add (abs_sum_le_card (U \ V) f hf) (abs_sum_le_card (V \ U) f hf)
    _ = ((U ∆ V).card : ℝ) := by rw [card_symmDiff_eq_sdiff_add, Nat.cast_add]

end Cancellation

section Translation

variable {G : Type uG} [Group G] [DecidableEq G]

def leftTranslate (h : G) (A : Finset G) : Finset G := A.image (fun g => h * g)

def boundaryRatio (A : Finset G) (h : G) : ℝ :=
  ((leftTranslate h A ∆ A).card : ℝ) / (A.card : ℝ)

theorem sum_leftTranslate (h : G) (A : Finset G) (f : G → ℝ) :
    (∑ g ∈ A, f (h * g)) = ∑ x ∈ leftTranslate h A, f x := by
  unfold leftTranslate
  exact (Finset.sum_image (fun _ _ _ _ hxy => mul_left_cancel hxy)).symm

@[simp] theorem card_leftTranslate (h : G) (A : Finset G) :
    (leftTranslate h A).card = A.card :=
  Finset.card_image_of_injective A (fun _ _ hxy => mul_left_cancel hxy)

theorem abs_sum_translate_sub_le (A : Finset G) (h : G) (f : G → ℝ)
    (hf : ∀ g, |f g| ≤ 1) :
    |(∑ g ∈ A, f (h * g)) - ∑ g ∈ A, f g| ≤
      ((leftTranslate h A ∆ A).card : ℝ) := by
  rw [sum_leftTranslate]
  exact abs_sum_sub_le_card_symmDiff (leftTranslate h A) A f hf

/-- The finite-translation inequality for every globally unit-bounded function. -/
theorem abs_realAvg_translate_sub_le (A : Finset G) (hA : A.Nonempty)
    (h : G) (f : G → ℝ) (hf : ∀ g, |f g| ≤ 1) :
    |realAvg A (fun g => f (h * g)) - realAvg A f| ≤ boundaryRatio A h := by
  have hc : 0 < (A.card : ℝ) := Nat.cast_pos.mpr (Finset.card_pos.mpr hA)
  rw [realAvg_eq_sum_div, realAvg_eq_sum_div, ← sub_div, abs_div, abs_of_pos hc]
  exact div_le_div_of_nonneg_right (abs_sum_translate_sub_le A h f hf) hc.le

/-- The real maximum requires an actual member of the fixed transport set. -/
def boundaryMax (S : Finset G) (hS : S.Nonempty) (A : Finset G) : ℝ := by
  classical
  exact (S.image (boundaryRatio A)).max' (hS.image _)

theorem boundaryMax_attained (S : Finset G) (hS : S.Nonempty) (A : Finset G) :
    ∃ h ∈ S, boundaryRatio A h = boundaryMax S hS A := by
  classical
  have hm : boundaryMax S hS A ∈ S.image (boundaryRatio A) :=
    Finset.max'_mem _ _
  exact Finset.mem_image.mp hm

theorem boundaryRatio_le_max (S : Finset G) (hS : S.Nonempty) (A : Finset G)
    {h : G} (hh : h ∈ S) : boundaryRatio A h ≤ boundaryMax S hS A := by
  classical
  exact (S.image (boundaryRatio A)).le_max' (boundaryRatio A h)
    (Finset.mem_image_of_mem _ hh)

theorem exists_boundary_ge_of_le_max (S : Finset G) (hS : S.Nonempty)
    (A : Finset G) {b : ℝ} (hb : b ≤ boundaryMax S hS A) :
    ∃ h ∈ S, b ≤ boundaryRatio A h := by
  obtain ⟨h, hh, hmax⟩ := boundaryMax_attained S hS A
  exact ⟨h, hh, hmax.symm ▸ hb⟩

end Translation

end ThompsonNonamenability

end

end OAI

end
end

section
section
namespace OAI

/-!
# Exact finite correlation and variance estimates

The diagonal and off-diagonal coefficients are exact finite counts. The mixed
sum has one exceptional parent column, hence D nested terms and D(D-1)
separated terms. Every count identity permits arbitrary signed coefficients.
The final cancellation imposes no positivity assumption on the common
correlation alpha.
-/

noncomputable section


namespace ThompsonNonamenability

open scoped BigOperators InnerProductSpace

variable {D : ℕ}

/-- One distinguished position and all the other positions, with signed values. -/
theorem sum_one_exception (i : Fin D) (b c : ℝ) :
    (∑ j : Fin D, if j = i then b else c) = b + ((D : ℝ) - 1) * c := by
  classical
  have hterm (j : Fin D) :
      (if j = i then b else c) = c + (if j = i then b - c else 0) := by
    by_cases h : j = i <;> simp [h]
  simp_rw [hterm]
  simp only [Finset.sum_add_distrib, Fintype.sum_ite_eq', Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-- D diagonal terms and D(D-1) off-diagonal terms, with no sign premise. -/
theorem sum_matrix_le (K : Fin D → Fin D → ℝ) (b c : ℝ)
    (hdiag : ∀ j, K j j ≤ b)
    (hoff : ∀ j k, j ≠ k → K j k ≤ c) :
    (∑ j, ∑ k, K j k) ≤
      (D : ℝ) * ((D : ℝ) - 1) * c + (D : ℝ) * b := by
  classical
  calc
    (∑ j, ∑ k, K j k) ≤ ∑ j : Fin D, ∑ k : Fin D, if k = j then b else c := by
      apply Finset.sum_le_sum
      intro j _
      apply Finset.sum_le_sum
      intro k _
      by_cases h : k = j
      · subst k
        simpa using hdiag j
      · simpa only [if_neg h] using hoff j k (Ne.symm h)
    _ = (D : ℝ) * ((D : ℝ) - 1) * c + (D : ℝ) * b := by
      simp_rw [sum_one_exception]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

/-- The exceptional column contributes D terms, irrespective of the row index. -/
theorem sum_fixed_column_ge (i : Fin D) (K : Fin D → Fin D → ℝ) (b c : ℝ)
    (hnested : ∀ j, b ≤ K j i)
    (hsep : ∀ j k, k ≠ i → c ≤ K j k) :
    (D : ℝ) * ((D : ℝ) - 1) * c + (D : ℝ) * b ≤ ∑ j, ∑ k, K j k := by
  classical
  calc
    (D : ℝ) * ((D : ℝ) - 1) * c + (D : ℝ) * b =
        ∑ _j : Fin D, ∑ k : Fin D, if k = i then b else c := by
      simp_rw [sum_one_exception]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring
    _ ≤ ∑ j, ∑ k, K j k := by
      apply Finset.sum_le_sum
      intro j _
      apply Finset.sum_le_sum
      intro k _
      by_cases h : k = i
      · subst k
        simpa using hnested j
      · simpa only [if_neg h] using hsep j k h

private theorem normalize_pair_total (hD : 0 < D) (b c : ℝ) :
    ((D : ℝ)⁻¹)^2 * ((D : ℝ) * ((D : ℝ) - 1) * c + (D : ℝ) * b) =
      (1 - (D : ℝ)⁻¹) * c + (D : ℝ)⁻¹ * b := by
  have hd : (D : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hD)
  field_simp [hd]

variable {G : Type uG} {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The literal finite average of the real inner product. -/
def corr (A : Finset G) (x y : G → E) : ℝ :=
  realAvg A (fun g => ⟪x g, y g⟫_ℝ)

theorem unit_inner_abs_le (x y : E) (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) :
    |⟪x, y⟫_ℝ| ≤ 1 := by
  calc
    |⟪x, y⟫_ℝ| ≤ ‖x‖ * ‖y‖ := abs_real_inner_le_norm x y
    _ ≤ 1 * 1 := mul_le_mul hx hy (norm_nonneg y) zero_le_one
    _ = 1 := by ring

theorem corr_abs_le_one (A : Finset G) (hA : A.Nonempty) (x y : G → E)
    (hx : ∀ g ∈ A, ‖x g‖ ≤ 1) (hy : ∀ g ∈ A, ‖y g‖ ≤ 1) :
    |corr A x y| ≤ 1 := by
  unfold corr
  apply abs_le.mpr
  constructor
  · apply const_le_realAvg A hA
    intro g hg
    exact (abs_le.mp (unit_inner_abs_le (x g) (y g) (hx g hg) (hy g hg))).1
  · apply realAvg_le_const A hA
    intro g hg
    exact (abs_le.mp (unit_inner_abs_le (x g) (y g) (hx g hg) (hy g hg))).2

theorem realAvg_norm_finMean_sq (A : Finset G) (x : G → Fin D → E) :
    realAvg A (fun g => ‖finMean (x g)‖^2) =
      ((D : ℝ)⁻¹)^2 * ∑ j, ∑ k, corr A (fun g => x g j) (fun g => x g k) := by
  simp only [norm_finMean_sq, realAvg_const_mul, realAvg_sum_univ, corr]

theorem corr_finMean (A : Finset G) (x y : G → Fin D → E) :
    corr A (fun g => finMean (x g)) (fun g => finMean (y g)) =
      ((D : ℝ)⁻¹)^2 * ∑ j, ∑ k, corr A (fun g => x g j) (fun g => y g k) := by
  simp only [corr, inner_finMean, pow_two, realAvg_const_mul, realAvg_sum_univ]

theorem realAvg_norm_sub_sq (A : Finset G) (x y : G → E) :
    realAvg A (fun g => ‖x g - y g‖^2) =
      realAvg A (fun g => ‖x g‖^2) - 2 * corr A x y +
        realAvg A (fun g => ‖y g‖^2) := by
  simp only [norm_sub_sq_real, realAvg_add, realAvg_sub, realAvg_const_mul, corr]

/-- Parent or sibling averages: the same exact diagonal count applies to both. -/
theorem realAvg_norm_finMean_sq_le (A : Finset G) (hA : A.Nonempty)
    (hD : 0 < D) (x : G → Fin D → E) (c : ℝ)
    (hx : ∀ g ∈ A, ∀ j, ‖x g j‖ ≤ 1)
    (hsep : ∀ j k, j ≠ k → corr A (fun g => x g j) (fun g => x g k) ≤ c) :
    realAvg A (fun g => ‖finMean (x g)‖^2) ≤
      (1 - (D : ℝ)⁻¹) * c + (D : ℝ)⁻¹ := by
  rw [realAvg_norm_finMean_sq]
  have hdiag (j : Fin D) : corr A (fun g => x g j) (fun g => x g j) ≤ 1 :=
    (abs_le.mp (corr_abs_le_one A hA _ _
      (fun g hg => hx g hg j) (fun g hg => hx g hg j))).2
  calc
    ((D : ℝ)⁻¹)^2 * ∑ j, ∑ k, corr A (fun g => x g j) (fun g => x g k) ≤
        ((D : ℝ)⁻¹)^2 * ((D : ℝ) * ((D : ℝ) - 1) * c + (D : ℝ) * 1) :=
      mul_le_mul_of_nonneg_left (sum_matrix_le _ 1 c hdiag hsep) (sq_nonneg _)
    _ = (1 - (D : ℝ)⁻¹) * c + (D : ℝ)⁻¹ := by
      simpa only [mul_one] using normalize_pair_total hD 1 c

/-- Only the designated parent column is uncontrolled in a mixed sum. -/
theorem corr_finMean_ge (A : Finset G) (hA : A.Nonempty) (hD : 0 < D)
    (i : Fin D) (z x : G → Fin D → E) (c : ℝ)
    (hz : ∀ g ∈ A, ∀ j, ‖z g j‖ ≤ 1)
    (hx : ∀ g ∈ A, ∀ k, ‖x g k‖ ≤ 1)
    (hsep : ∀ j k, k ≠ i → c ≤ corr A (fun g => z g j) (fun g => x g k)) :
    (1 - (D : ℝ)⁻¹) * c - (D : ℝ)⁻¹ ≤
      corr A (fun g => finMean (z g)) (fun g => finMean (x g)) := by
  have hnested (j : Fin D) : -1 ≤ corr A (fun g => z g j) (fun g => x g i) :=
    (abs_le.mp (corr_abs_le_one A hA _ _
      (fun g hg => hz g hg j) (fun g hg => hx g hg i))).1
  calc
    (1 - (D : ℝ)⁻¹) * c - (D : ℝ)⁻¹ =
        ((D : ℝ)⁻¹)^2 * ((D : ℝ) * ((D : ℝ) - 1) * c + (D : ℝ) * (-1)) := by
      rw [normalize_pair_total hD]
      ring
    _ ≤ ((D : ℝ)⁻¹)^2 * ∑ j, ∑ k, corr A (fun g => z g j) (fun g => x g k) :=
      mul_le_mul_of_nonneg_left (sum_fixed_column_ge i _ (-1) c hnested hsep)
        (sq_nonneg _)
    _ = corr A (fun g => finMean (z g)) (fun g => finMean (x g)) :=
      (corr_finMean A z x).symm

/-- The finite Hilbert variance bound with exact cancellation of signed alpha. -/
theorem finite_variance_bound (A : Finset G) (hA : A.Nonempty) (hD : 0 < D)
    (x : G → Fin D → E) (y : G → Fin D → Fin D → E) (α η : ℝ)
    (hx : ∀ g ∈ A, ∀ k, ‖x g k‖ ≤ 1)
    (hy : ∀ g ∈ A, ∀ i j, ‖y g i j‖ ≤ 1)
    (hparent : ∀ j k, j ≠ k →
      |corr A (fun g => x g j) (fun g => x g k) - α| ≤ η)
    (hchild : ∀ i j k, j ≠ k →
      |corr A (fun g => y g i j) (fun g => y g i k) - α| ≤ η)
    (hmixed : ∀ i j k, k ≠ i →
      |corr A (fun g => y g i j) (fun g => x g k) - α| ≤ η) :
    ∀ i, realAvg A (fun g => ‖finMean (y g i) - finMean (x g)‖^2) ≤
      4 / (D : ℝ) + 4 * (1 - 1 / (D : ℝ)) * η := by
  intro i
  have hp := realAvg_norm_finMean_sq_le A hA hD x (α + η) hx (by
    intro j k hjk
    have h := (abs_le.mp (hparent j k hjk)).2
    linarith)
  have hq := realAvg_norm_finMean_sq_le A hA hD (fun g => y g i) (α + η)
    (fun g hg => hy g hg i) (by
      intro j k hjk
      have h := (abs_le.mp (hchild i j k hjk)).2
      linarith)
  have hm := corr_finMean_ge A hA hD i (fun g => y g i) x (α - η)
    (fun g hg => hy g hg i) hx (by
      intro j k hki
      have h := (abs_le.mp (hmixed i j k hki)).1
      linarith)
  rw [realAvg_norm_sub_sq]
  calc
    realAvg A (fun g => ‖finMean (y g i)‖^2) -
        2 * corr A (fun g => finMean (y g i)) (fun g => finMean (x g)) +
        realAvg A (fun g => ‖finMean (x g)‖^2) ≤
        ((1 - (D : ℝ)⁻¹) * (α + η) + (D : ℝ)⁻¹) -
          2 * ((1 - (D : ℝ)⁻¹) * (α - η) - (D : ℝ)⁻¹) +
          ((1 - (D : ℝ)⁻¹) * (α + η) + (D : ℝ)⁻¹) := by
      linarith only [hp, hq, hm]
    _ = 4 / (D : ℝ) + 4 * (1 - 1 / (D : ℝ)) * η := by
      simp only [div_eq_mul_inv, one_mul]
      ring

end ThompsonNonamenability

end

end OAI

end
end

section
section
namespace OAI

/-!
# Globally defined colors of the actual Thompson-group images

A non-basic image, or a basic image failing the simultaneous family respect
condition, receives zero. Thus every correlation is bounded on the entire
actual group, including outside a finite set used for averaging.
-/

noncomputable section

open scoped InnerProductSpace


namespace ThompsonNonamenability

local instance : DecidableEq F := Classical.decEq F

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {D : ℕ}

/-- The genuine partial image of the uniform partition, made total with `none`. -/
def imagePartitionOption (g : F) (n : ℕ) : Option BasicPartition := by
  classical
  exact if hg : ImageBasic g n then some (imagePartition g n hg) else none

/-- One condition for the whole actual parent/child family at a group element. -/
def GlobalAdmissible (D n : ℕ) (g : F) : Prop :=
  ∃ hg : ImageBasic g n, PartitionAdmissible D (imagePartition g n hg)

def globalColor (hD : 0 < D) (f : UnitBall E → UnitBall E)
    (n : ℕ) (q : IntervalIndex D) (g : F) : UnitBall E :=
  optionFamilyColor hD f (imagePartitionOption g n) q

theorem globalColor_of_imageBasic (hD : 0 < D) (f : UnitBall E → UnitBall E)
    (n : ℕ) (g : F) (hg : ImageBasic g n) (q : IntervalIndex D) :
    globalColor hD f n q g = partitionFamilyColor hD f (imagePartition g n hg) q := by
  simp only [globalColor, imagePartitionOption, dif_pos hg, optionFamilyColor_some]

theorem globalColor_of_image_admissible (hD : 0 < D)
    (f : UnitBall E → UnitBall E) (n : ℕ) (g : F) (hg : ImageBasic g n)
    (hp : PartitionAdmissible D (imagePartition g n hg)) (q : IntervalIndex D) :
    globalColor hD f n q g =
      partitionColor (selectedInterval D) (selectedInterval_internal D) hD f
        ((imagePartition g n hg).restrict (familyInterval D q) (hp q)) := by
  rw [globalColor_of_imageBasic hD f n g hg q]
  exact partitionFamilyColor_of_admissible hD f _ hp q

theorem globalColor_norm_le (hD : 0 < D) (f : UnitBall E → UnitBall E)
    (n : ℕ) (q : IntervalIndex D) (g : F) :
    ‖(globalColor hD f n q g : E)‖ ≤ 1 :=
  (globalColor hD f n q g).property

/-- The actual finite group set has one common admissibility level. -/
theorem eventually_global_admissible (D : ℕ) (K : Finset F) :
    ∃ N, ∀ n ≥ N, ∀ g ∈ K, GlobalAdmissible D n g := by
  obtain ⟨N, hN⟩ := eventually_image_respects K (intervalFamily D)
  refine ⟨N, ?_⟩
  intro n hn g hg
  obtain ⟨hb, hr⟩ := hN n hn g hg
  exact ⟨hb, fun q => hr (familyInterval D q) (familyInterval_mem D q)⟩

theorem exists_common_admissible (D : ℕ) (K : Finset F) :
    ∃ n, ∀ g ∈ K, GlobalAdmissible D n g := by
  obtain ⟨N, hN⟩ := eventually_global_admissible D K
  exact ⟨N, hN N le_rfl⟩

/-- The exact recursive identity at every admissible actual group point. -/
theorem globalColor_parent (hD : 0 < D) (f : UnitBall E → UnitBall E)
    (n : ℕ) (g : F) (hg : GlobalAdmissible D n g) (i : Fin D) :
    globalColor hD f n (.inl i) g =
      f (ballMean hD (fun j => globalColor hD f n (.inr (i, j)) g)) := by
  obtain ⟨hb, hp⟩ := hg
  simp only [globalColor_of_imageBasic hD f n g hb]
  exact partitionFamilyColor_parent hD f _ hp i

/-- Source and target admissibility suffice; the transport need not preserve
any other selected interval. -/
theorem globalColor_covariance (hD : 0 < D) (f : UnitBall E → UnitBall E)
    (n : ℕ) (h g : F) (q r : IntervalIndex D)
    (hc : CarriesAffinely h (familyInterval D q) (familyInterval D r))
    (hg : GlobalAdmissible D n g) (hhg : GlobalAdmissible D n (h * g)) :
    globalColor hD f n q g = globalColor hD f n r (h * g) := by
  obtain ⟨hb, hp⟩ := hg
  obtain ⟨hhb, hhp⟩ := hhg
  rw [globalColor_of_image_admissible hD f n g hb hp q,
    globalColor_of_image_admissible hD f n (h * g) hhb hhp r]
  apply congrArg (partitionColor (selectedInterval D) (selectedInterval_internal D) hD f)
  exact (image_restrict_covariance h g n (familyInterval D q) (familyInterval D r)
    hc hb hhb (hp q) (hhp r)).symm

/-- A real correlation on all of the actual group. -/
def globalCorrelation (hD : 0 < D) (f : UnitBall E → UnitBall E)
    (n : ℕ) (q r : IntervalIndex D) (g : F) : ℝ :=
  ⟪(globalColor hD f n q g : E), globalColor hD f n r g⟫_ℝ

theorem globalCorrelation_abs_le_one (hD : 0 < D)
    (f : UnitBall E → UnitBall E) (n : ℕ) (q r : IntervalIndex D) (g : F) :
    |globalCorrelation hD f n q r g| ≤ 1 :=
  unit_inner_abs_le _ _ (globalColor_norm_le hD f n q g)
    (globalColor_norm_le hD f n r g)

theorem globalCorrelation_covariance (hD : 0 < D) (f : UnitBall E → UnitBall E)
    (n : ℕ) (h g : F) (q r q' r' : IntervalIndex D)
    (hq : CarriesAffinely h (familyInterval D q) (familyInterval D q'))
    (hr : CarriesAffinely h (familyInterval D r) (familyInterval D r'))
    (hg : GlobalAdmissible D n g) (hhg : GlobalAdmissible D n (h * g)) :
    globalCorrelation hD f n q r g = globalCorrelation hD f n q' r' (h * g) := by
  unfold globalCorrelation
  rw [globalColor_covariance hD f n h g q q' hq hg hhg,
    globalColor_covariance hD f n h g r r' hr hg hhg]

/-- Exact affine covariance and global boundedness imply the finite comparison. -/
theorem globalCorrelation_translate_bound (hD : 0 < D)
    (f : UnitBall E → UnitBall E) (n : ℕ) (A : Finset F) (hA : A.Nonempty)
    (h : F) (q r q' r' : IntervalIndex D)
    (hq : CarriesAffinely h (familyInterval D q) (familyInterval D q'))
    (hr : CarriesAffinely h (familyInterval D r) (familyInterval D r'))
    (hg : ∀ g ∈ A, GlobalAdmissible D n g)
    (hhg : ∀ g ∈ A, GlobalAdmissible D n (h * g)) :
    |realAvg A (globalCorrelation hD f n q r) -
      realAvg A (globalCorrelation hD f n q' r')| ≤ boundaryRatio A h := by
  classical
  have heq : realAvg A (globalCorrelation hD f n q r) =
      realAvg A (fun g => globalCorrelation hD f n q' r' (h * g)) := by
    apply realAvg_congr
    intro g hmem
    exact globalCorrelation_covariance hD f n h g q r q' r' hq hr
      (hg g hmem) (hhg g hmem)
  rw [heq]
  exact abs_realAvg_translate_sub_le A hA h (globalCorrelation hD f n q' r')
    (globalCorrelation_abs_le_one hD f n q' r')

end ThompsonNonamenability

end

end OAI

end
end

section
section
namespace OAI

/-!
# Consecutive dyadic cells

A chain is an ordered list of actual basic intervals whose consecutive
endpoints agree. Its endpoints and coverage are proved from this data.
-/

namespace ThompsonNonamenability

noncomputable section

/-- A finite list of consecutive cells starts at `a` and ends at `b`.
The empty list represents a gap of length zero. -/
def GapChain : ℝ → ℝ → List BasicInterval → Prop
  | a, b, [] => a = b
  | a, b, I :: L => I.left = a ∧ GapChain I.right b L

namespace GapChain

@[simp] theorem nil_iff {a b : ℝ} : GapChain a b [] ↔ a = b := Iff.rfl

@[simp] theorem cons_iff {a b : ℝ} {I : BasicInterval} {L : List BasicInterval} :
    GapChain a b (I :: L) ↔ I.left = a ∧ GapChain I.right b L := Iff.rfl

@[simp] theorem singleton_iff {a b : ℝ} {I : BasicInterval} :
    GapChain a b [I] ↔ I.left = a ∧ I.right = b := Iff.rfl

theorem append {a b c : ℝ} {L M : List BasicInterval}
    (hL : GapChain a b L) (hM : GapChain b c M) : GapChain a c (L ++ M) := by
  induction L generalizing a with
  | nil =>
      change a = b at hL
      subst a
      exact hM
  | cons I L ih =>
      exact ⟨hL.1, ih hL.2⟩

theorem le_endpoints {a b : ℝ} {L : List BasicInterval}
    (h : GapChain a b L) : a ≤ b := by
  induction L generalizing a with
  | nil => exact le_of_eq h
  | cons I L ih =>
      calc
        a = I.left := h.1.symm
        _ ≤ I.right := I.left_lt_right.le
        _ ≤ b := ih h.2

theorem left_le_of_mem {a b : ℝ} {L : List BasicInterval}
    (h : GapChain a b L) {I : BasicInterval} (hI : I ∈ L) : a ≤ I.left := by
  induction L generalizing a with
  | nil => exact False.elim (List.not_mem_nil hI)
  | cons J L ih =>
      rcases List.mem_cons.mp hI with rfl | hI
      · exact le_of_eq h.1.symm
      · calc
          a = J.left := h.1.symm
          _ ≤ J.right := J.left_lt_right.le
          _ ≤ I.left := ih h.2 hI

end GapChain

/-- A nonempty ordered partition of an actual interval by basic dyadic cells. -/
structure DyadicGapPartition (a b : ℝ) where
  cells : List BasicInterval
  chain : GapChain a b cells
  nonempty : cells ≠ []

namespace DyadicGapPartition

end DyadicGapPartition

end

end ThompsonNonamenability

end OAI

end
end

section
section
namespace OAI

/-!
# Partitions of positive dyadic gaps

The initial partition consists of consecutive cells of a common dyadic grid.
Splitting one cell gives exactly one additional cell. Thus each pair of gaps
can be partitioned into the same number of cells independently.
-/

namespace ThompsonNonamenability

noncomputable section

/-- Consecutive cells with indices `A, ..., A+c-1` on grid level `n`. -/
def uniformGapCells (n A c : ℕ) (h : A + c ≤ 2 ^ n) : List BasicInterval :=
  match c with
  | 0 => []
  | c + 1 =>
      (⟨n, ⟨A, by omega⟩⟩ : BasicInterval) ::
        uniformGapCells n (A + 1) c (by omega)
termination_by c

@[simp] theorem uniformGapCells_length (n A c : ℕ) (h : A + c ≤ 2 ^ n) :
    (uniformGapCells n A c h).length = c := by
  induction c generalizing A with
  | zero => simp [uniformGapCells]
  | succ c ih => simp [uniformGapCells, ih]

theorem uniformGapCells_chain (n A c : ℕ) (h : A + c ≤ 2 ^ n) :
    GapChain ((A : ℝ) / (2 : ℝ) ^ n)
      (((A + c : ℕ) : ℝ) / (2 : ℝ) ^ n) (uniformGapCells n A c h) := by
  induction c generalizing A with
  | zero => simp [uniformGapCells]
  | succ c ih =>
      simp only [uniformGapCells]
      refine ⟨rfl, ?_⟩
      simpa [BasicInterval.right, Nat.cast_add, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using ih (A + 1) (by omega)

/-- An actual basic-cell partition of any positive dyadic subinterval. -/
theorem exists_dyadicGapPartition {a b : ℝ}
    (ha : IsDyadic a) (hb : IsDyadic b)
    (h0 : 0 ≤ a) (hab : a < b) (h1 : b ≤ 1) :
    Nonempty (DyadicGapPartition a b) := by
  obtain ⟨ka, na, hka⟩ := ha
  obtain ⟨kb, nb, hkb⟩ := hb
  obtain ⟨ka', hka'⟩ := dyadic_raise_denominator ⟨ka, hka⟩ nb
  obtain ⟨kb', hkb'⟩ := dyadic_raise_denominator ⟨kb, hkb⟩ na
  have hkb'' : b = (kb' : ℝ) / (2 : ℝ) ^ (na + nb) := by
    simpa only [Nat.add_comm nb na] using hkb'
  obtain ⟨A, hAmax, hA⟩ := dyadic_nat_numerator hka' h0 (hab.le.trans h1)
  obtain ⟨B, hBmax, hB⟩ := dyadic_nat_numerator hkb'' (h0.trans hab.le) h1
  have hABr : (A : ℝ) < (B : ℝ) := by
    apply (div_lt_div_iff_of_pos_right (pow_pos (by norm_num : (0 : ℝ) < 2)
      (na + nb))).1
    rw [← hA, ← hB]
    exact hab
  have hAB : A < B := by exact_mod_cast hABr
  have hsum : A + (B - A) = B := by omega
  let cells := uniformGapCells (na + nb) A (B - A) (by omega)
  have hc : GapChain a b cells := by
    simpa only [cells, hsum, ← hA, ← hB] using
      uniformGapCells_chain (na + nb) A (B - A) (by omega)
  refine ⟨⟨cells, hc, ?_⟩⟩
  intro he
  have hlen := congrArg List.length he
  simp only [cells, uniformGapCells_length, List.length_nil] at hlen
  omega

namespace BasicInterval

/-- The left half of an actual basic interval. -/
def splitLeft (I : BasicInterval) : BasicInterval :=
  I.comp ⟨1, ⟨0, by decide⟩⟩

/-- The right half of an actual basic interval. -/
def splitRight (I : BasicInterval) : BasicInterval :=
  I.comp ⟨1, ⟨1, by decide⟩⟩

@[simp] theorem splitLeft_left (I : BasicInterval) : I.splitLeft.left = I.left := by
  rw [splitLeft, left_comp]
  have h : (⟨1, ⟨0, by decide⟩⟩ : BasicInterval).left = 0 := by
    norm_num [left]
  rw [h, chart_zero]

@[simp] theorem splitRight_right (I : BasicInterval) : I.splitRight.right = I.right := by
  rw [splitRight, right_comp]
  have h : (⟨1, ⟨1, by decide⟩⟩ : BasicInterval).right = 1 := by
    norm_num [right]
  rw [h, chart_one]

theorem split_adjacent (I : BasicInterval) : I.splitLeft.right = I.splitRight.left := by
  rw [splitLeft, splitRight, right_comp, left_comp]
  congr 1
  norm_num [right, left]

theorem splitLeft_contained (I : BasicInterval) : I.splitLeft.Contained I :=
  I.comp_contained _

theorem splitRight_contained (I : BasicInterval) : I.splitRight.Contained I :=
  I.comp_contained _

end BasicInterval

/-- Every cell in the refined list lies in an original cell. -/
def GapRefines (newCells oldCells : List BasicInterval) : Prop :=
  ∀ J ∈ newCells, ∃ I ∈ oldCells, J.Contained I

namespace GapRefines

theorem refl (L : List BasicInterval) : GapRefines L L := by
  intro I hI
  exact ⟨I, hI, I.contained_refl⟩

theorem trans {L M N : List BasicInterval} (hLM : GapRefines L M)
    (hMN : GapRefines M N) : GapRefines L N := by
  intro I hI
  obtain ⟨J, hJ, hIJ⟩ := hLM I hI
  obtain ⟨K, hK, hJK⟩ := hMN J hJ
  exact ⟨K, hK, hIJ.trans hJK⟩

end GapRefines

namespace GapChain

theorem split_head {a b : ℝ} {I : BasicInterval} {L : List BasicInterval}
    (h : GapChain a b (I :: L)) :
    GapChain a b (I.splitLeft :: I.splitRight :: L) := by
  rcases h with ⟨hleft, htail⟩
  refine ⟨I.splitLeft_left.trans hleft, I.split_adjacent.symm, ?_⟩
  simpa only [BasicInterval.splitRight_right] using htail

theorem split_head_refines (I : BasicInterval) (L : List BasicInterval) :
    GapRefines (I.splitLeft :: I.splitRight :: L) (I :: L) := by
  intro J hJ
  simp only [List.mem_cons] at hJ
  rcases hJ with rfl | rfl | hJ
  · exact ⟨I, List.mem_cons_self, I.splitLeft_contained⟩
  · exact ⟨I, List.mem_cons_self, I.splitRight_contained⟩
  · exact ⟨J, List.mem_cons_of_mem I hJ, J.contained_refl⟩

/-- Bisection increases a nonempty chain's cardinality by exactly one. -/
theorem exists_succ_length {a b : ℝ} {L : List BasicInterval}
    (h : GapChain a b L) (hne : L ≠ []) :
    ∃ M : List BasicInterval, GapChain a b M ∧
      M.length = L.length + 1 ∧ GapRefines M L := by
  cases L with
  | nil => exact False.elim (hne rfl)
  | cons I L =>
      exact ⟨I.splitLeft :: I.splitRight :: L, h.split_head,
        by simp [Nat.add_comm, Nat.add_left_comm], split_head_refines I L⟩

/-- Any prescribed nonnegative number of extra cells can be obtained by bisection. -/
theorem exists_length_add {a b : ℝ} {L : List BasicInterval}
    (h : GapChain a b L) (hne : L ≠ []) (k : ℕ) :
    ∃ M : List BasicInterval, GapChain a b M ∧
      M.length = L.length + k ∧ GapRefines M L := by
  induction k with
  | zero => exact ⟨L, h, by simp, GapRefines.refl L⟩
  | succ k ih =>
      obtain ⟨M, hM, hlen, href⟩ := ih
      have hMne : M ≠ [] := by
        intro hempty
        have hL : L.length = 0 := by simp only [hempty, List.length_nil] at hlen; omega
        exact hne (List.length_eq_zero_iff.mp hL)
      obtain ⟨N, hN, hNlen, hNref⟩ := hM.exists_succ_length hMne
      refine ⟨N, hN, ?_, hNref.trans href⟩
      omega

theorem exists_length_ge {a b : ℝ} {L : List BasicInterval}
    (h : GapChain a b L) (hne : L ≠ []) {n : ℕ} (hn : L.length ≤ n) :
    ∃ M : List BasicInterval, GapChain a b M ∧ M.length = n ∧ GapRefines M L := by
  obtain ⟨M, hM, hlen, href⟩ := h.exists_length_add hne (n - L.length)
  exact ⟨M, hM, by omega, href⟩

end GapChain

namespace DyadicGapPartition

theorem exists_refinement_card {a b : ℝ} (P : DyadicGapPartition a b)
    {n : ℕ} (hn : P.cells.length ≤ n) :
    ∃ Q : DyadicGapPartition a b, Q.cells.length = n ∧ GapRefines Q.cells P.cells := by
  obtain ⟨M, hM, hlen, href⟩ := P.chain.exists_length_ge P.nonempty hn
  have hMne : M ≠ [] := by
    intro hempty
    have hnzero : n = 0 := by simpa only [hempty, List.length_nil] using hlen.symm
    have hpzero : P.cells.length = 0 := by omega
    exact P.nonempty (List.length_eq_zero_iff.mp hpzero)
  exact ⟨⟨M, hM, hMne⟩, hlen, href⟩

/-- Equalization is performed for this pair of gaps, with both refinements retained. -/
theorem equalize {a b c d : ℝ} (P : DyadicGapPartition a b) (Q : DyadicGapPartition c d) :
    ∃ (P' : DyadicGapPartition a b) (Q' : DyadicGapPartition c d),
      P'.cells.length = Q'.cells.length ∧
      GapRefines P'.cells P.cells ∧ GapRefines Q'.cells Q.cells := by
  obtain ⟨P', hP', hrefP⟩ := P.exists_refinement_card (Nat.le_max_left P.cells.length Q.cells.length)
  obtain ⟨Q', hQ', hrefQ⟩ := Q.exists_refinement_card (Nat.le_max_right P.cells.length Q.cells.length)
  exact ⟨P', Q', hP'.trans hQ'.symm, hrefP, hrefQ⟩

end DyadicGapPartition

theorem exists_equal_length_partitions {a b c d : ℝ}
    (ha : IsDyadic a) (hb : IsDyadic b) (hc : IsDyadic c) (hd : IsDyadic d)
    (ha0 : 0 ≤ a) (hb1 : b ≤ 1) (hc0 : 0 ≤ c) (hd1 : d ≤ 1)
    (hab : a < b) (hcd : c < d) :
    ∃ P : DyadicGapPartition a b, ∃ Q : DyadicGapPartition c d,
      P.cells.length = Q.cells.length := by
  obtain ⟨P⟩ := exists_dyadicGapPartition ha hb ha0 hab hb1
  obtain ⟨Q⟩ := exists_dyadicGapPartition hc hd hc0 hcd hd1
  obtain ⟨P', Q', hlen, _, _⟩ := P.equalize Q
  exact ⟨P', Q', hlen⟩

end

end ThompsonNonamenability

end OAI

end
end

section
section
namespace OAI

/-!
# Affine maps between basic dyadic intervals

Each pair of basic intervals determines an increasing affine map of the real
line. It carries endpoints and charts to their counterparts, and its slope is
an integral power of two.
-/

noncomputable section

namespace ThompsonNonamenability

namespace OrderedPLInterpolation

def affine (I J : BasicInterval) (x : ℝ) : ℝ :=
  J.left + (J.length / I.length) * (x - I.left)

@[simp] theorem affine_left (I J : BasicInterval) :
    affine I J I.left = J.left := by
  simp [affine]

@[simp] theorem affine_right (I J : BasicInterval) :
    affine I J I.right = J.right := by
  unfold affine
  rw [← I.length_eq_right_sub_left]
  rw [div_mul_cancel₀ _ (ne_of_gt I.length_pos)]
  rw [J.length_eq_right_sub_left]
  ring

theorem affine_strictMono (I J : BasicInterval) : StrictMono (affine I J) := by
  intro x y hxy
  exact add_lt_add_right
    (mul_lt_mul_of_pos_left (sub_lt_sub_right hxy I.left)
      (div_pos J.length_pos I.length_pos)) J.left

@[simp] theorem affine_inverse (I J : BasicInterval) (x : ℝ) :
    affine J I (affine I J x) = x := by
  unfold affine
  field_simp [ne_of_gt I.length_pos, ne_of_gt J.length_pos]
  ring

@[simp] theorem affine_chart (I J : BasicInterval) (x : ℝ) :
    affine I J (I.chart x) = J.chart x := by
  rw [I.chart_eq_left_add_length_mul, J.chart_eq_left_add_length_mul]
  unfold affine
  field_simp [ne_of_gt I.length_pos]
  ring

theorem affine_slope_zpow (I J : BasicInterval) :
    J.length / I.length = (2 : ℝ) ^ ((I.depth : ℤ) - (J.depth : ℤ)) := by
  rw [zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0)]
  simp only [zpow_natCast, BasicInterval.length, inv_div_inv]

end OrderedPLInterpolation

end ThompsonNonamenability

end

end OAI

end
end

section
section
namespace OAI

/-!
# Indexed knots of an ordered dyadic chain

An actual consecutive list of dyadic cells covering `[0,1]` gives a strictly
increasing subdivision indexed by that same list. The two endpoints of its
`i`th piece are exactly the endpoints of the `i`th listed cell.
-/

noncomputable section

namespace ThompsonNonamenability

namespace GapChain

/-- The initial endpoint followed by the right endpoints of the cells. -/
def realKnots : (a : ℝ) → (L : List BasicInterval) → Fin (L.length + 1) → ℝ
  | a, [], _ => a
  | a, I :: L, i => Fin.cases a (realKnots I.right L) i

@[simp] theorem realKnots_zero (a : ℝ) (L : List BasicInterval) :
    realKnots a L 0 = a := by
  cases L <;> rfl

/-- The right knot of each indexed piece is its actual right endpoint. -/
theorem realKnots_succ (a : ℝ) (L : List BasicInterval) (i : Fin L.length) :
    realKnots a L i.succ = (L.get i).right := by
  induction L generalizing a with
  | nil => exact Fin.elim0 i
  | cons I L ih =>
      refine Fin.cases ?_ (fun j => ?_) i
      · change realKnots I.right L 0 = I.right
        exact realKnots_zero I.right L
      · change realKnots I.right L j.succ = (L.get j).right
        exact ih I.right j

/-- The chain equalities identify each left knot with its listed cell. -/
theorem realKnots_castSucc {a b : ℝ} {L : List BasicInterval}
    (h : GapChain a b L) (i : Fin L.length) :
    realKnots a L i.castSucc = (L.get i).left := by
  induction L generalizing a with
  | nil => exact Fin.elim0 i
  | cons I L ih =>
      refine Fin.cases ?_ (fun j => ?_) i
      · change a = I.left
        exact h.1.symm
      · change realKnots I.right L j.castSucc = (L.get j).left
        exact ih h.2 j

theorem realKnots_last {a b : ℝ} {L : List BasicInterval}
    (h : GapChain a b L) : realKnots a L (Fin.last L.length) = b := by
  induction L generalizing a with
  | nil => exact h
  | cons I L ih =>
      change realKnots I.right L (Fin.last L.length) = b
      exact ih h.2

theorem strictMono_realKnots {a b : ℝ} {L : List BasicInterval}
    (h : GapChain a b L) : StrictMono (realKnots a L) := by
  apply Fin.strictMono_iff_lt_succ.mpr
  intro i
  rw [realKnots_castSucc h i, realKnots_succ]
  exact (L.get i).left_lt_right

theorem length_pos {L : List BasicInterval} (h : GapChain 0 1 L) :
    0 < L.length := by
  cases L with
  | nil => exact False.elim (zero_ne_one h)
  | cons I L => exact Nat.zero_lt_succ _

theorem realKnots_mem_unit {L : List BasicInterval} (h : GapChain 0 1 L)
    (i : Fin (L.length + 1)) : realKnots 0 L i ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · have hi := h.strictMono_realKnots.monotone (Fin.zero_le i)
    simpa only [realKnots_zero] using hi
  · have hi := h.strictMono_realKnots.monotone (Fin.le_last i)
    simpa only [realKnots_last h] using hi

theorem isDyadic_realKnots (L : List BasicInterval) (i : Fin (L.length + 1)) :
    IsDyadic (realKnots 0 L i) := by
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa only [realKnots_zero] using isDyadic_zero
  · rw [realKnots_succ]
    refine ⟨((L.get j).index.val : ℤ) + 1, (L.get j).depth, ?_⟩
    simp only [BasicInterval.right, Int.cast_add, Int.cast_natCast, Int.cast_one]

end GapChain

/-- A subdivision whose indexing agrees with an actual ordered cell list. -/
structure ChainSubdivision (L : List BasicInterval) where
  positive : 0 < L.length
  knots : Fin (L.length + 1) → UnitInterval
  strictMono_knots : StrictMono knots
  first : knots 0 = unitIntervalZero
  last : knots (Fin.last L.length) = unitIntervalOne
  dyadic : ∀ i, IsDyadic (knots i : ℝ)
  cover : ∀ x : UnitInterval, ∃ i : Fin L.length,
    knots i.castSucc ≤ x ∧ x ≤ knots i.succ
  left_eq : ∀ i : Fin L.length, (knots i.castSucc : ℝ) = (L.get i).left
  right_eq : ∀ i : Fin L.length, (knots i.succ : ℝ) = (L.get i).right

namespace GapChain

/-- Construct all subdivision data from the chain equalities. -/
def toSubdivision {L : List BasicInterval} (h : GapChain 0 1 L) :
    ChainSubdivision L := by
  let knots : Fin (L.length + 1) → UnitInterval :=
    fun i => ⟨realKnots 0 L i, h.realKnots_mem_unit i⟩
  have hfirst : knots 0 = unitIntervalZero := by
    apply Subtype.ext
    exact realKnots_zero 0 L
  have hlast : knots (Fin.last L.length) = unitIntervalOne := by
    apply Subtype.ext
    exact realKnots_last h
  exact
    { positive := h.length_pos
      knots := knots
      strictMono_knots := fun _ _ hij => h.strictMono_realKnots hij
      first := hfirst
      last := hlast
      dyadic := isDyadic_realKnots L
      cover := SortedSubdivision.cover_of_endpoints h.length_pos knots hfirst hlast
      left_eq := realKnots_castSucc h
      right_eq := realKnots_succ 0 L }

end GapChain

namespace ChainSubdivision

end ChainSubdivision

end ThompsonNonamenability

end

end OAI

end
end

section
section
namespace OAI

/-!
# Actual interpolation of ordered dyadic partitions

Matched cells determine affine maps. They are glued at their common endpoints,
and the reverse matching is their inverse. Restricting the resulting real
order isomorphism gives the literal interval homeomorphism.
-/

noncomputable section

namespace ThompsonNonamenability

namespace OrderedPLInterpolation

def chainMap (b d : ℝ) : List BasicInterval → List BasicInterval → ℝ → ℝ
  | [], _, x => x + (d - b)
  | _ :: _, [], x => x + (d - b)
  | I :: L, J :: R, x =>
      if x ≤ I.right then affine I J x else chainMap b d L R x

theorem chainMap_start {a b c d : ℝ} {L R : List BasicInterval}
    (hL : GapChain a b L) (hR : GapChain c d R) (hlen : L.length = R.length) :
    chainMap b d L R a = c := by
  cases L with
  | nil =>
      have hnil : R = [] := List.length_eq_zero_iff.mp hlen.symm
      subst R
      change a = b at hL
      change c = d at hR
      simp only [chainMap, hL, hR]
      ring
  | cons I L =>
      cases R with
      | nil => simp at hlen
      | cons J R =>
          change I.left = a ∧ GapChain I.right b L at hL
          change J.left = c ∧ GapChain J.right d R at hR
          rw [← hL.1]
          simp only [chainMap, if_pos I.left_lt_right.le, affine_left, hR.1]

theorem chainMap_eq_tail {b d x : ℝ} {I J : BasicInterval}
    {L R : List BasicInterval} (hL : GapChain I.right b L)
    (hR : GapChain J.right d R) (hlen : L.length = R.length)
    (hx : I.right ≤ x) :
    chainMap b d (I :: L) (J :: R) x = chainMap b d L R x := by
  by_cases h : x ≤ I.right
  · have heq : x = I.right := le_antisymm h hx
    subst x
    rw [chainMap, if_pos le_rfl, affine_right, chainMap_start hL hR hlen]
  · rw [chainMap, if_neg h]

theorem chainMap_end {a b c d : ℝ} {L R : List BasicInterval}
    (hL : GapChain a b L) (hR : GapChain c d R) (hlen : L.length = R.length) :
    chainMap b d L R b = d := by
  induction L generalizing a c R with
  | nil =>
      simp only [chainMap]
      ring
  | cons I L ih =>
      cases R with
      | nil => simp at hlen
      | cons J R =>
          have ht : L.length = R.length := Nat.succ.inj hlen
          rw [chainMap_eq_tail hL.2 hR.2 ht hL.2.le_endpoints]
          exact ih hL.2 hR.2 ht

theorem chainMap_strictMono {a b c d : ℝ} {L R : List BasicInterval}
    (hL : GapChain a b L) (hR : GapChain c d R) (hlen : L.length = R.length) :
    StrictMono (chainMap b d L R) := by
  induction L generalizing a c R with
  | nil =>
      intro x y hxy
      exact add_lt_add_left hxy _
  | cons I L ih =>
      cases R with
      | nil => simp at hlen
      | cons J R =>
          have ht : L.length = R.length := Nat.succ.inj hlen
          have hm := ih hL.2 hR.2 ht
          have hb := chainMap_start hL.2 hR.2 ht
          intro x y hxy
          change (if x ≤ I.right then affine I J x else chainMap b d L R x) <
            (if y ≤ I.right then affine I J y else chainMap b d L R y)
          by_cases hx : x ≤ I.right
          · rw [if_pos hx]
            by_cases hy : y ≤ I.right
            · rw [if_pos hy]
              exact affine_strictMono I J hxy
            · rw [if_neg hy]
              calc
                affine I J x ≤ affine I J I.right :=
                  (affine_strictMono I J).monotone hx
                _ = J.right := affine_right I J
                _ = chainMap b d L R I.right := hb.symm
                _ < chainMap b d L R y := hm (lt_of_not_ge hy)
          · have hy : ¬ y ≤ I.right := fun hy => hx (hxy.le.trans hy)
            rw [if_neg hx, if_neg hy]
            exact hm hxy

theorem chainMap_inverse {a b c d : ℝ} {L R : List BasicInterval}
    (hL : GapChain a b L) (hR : GapChain c d R) (hlen : L.length = R.length)
    (x : ℝ) : chainMap d b R L (chainMap b d L R x) = x := by
  induction L generalizing a c R with
  | nil =>
      have hnil : R = [] := List.length_eq_zero_iff.mp hlen.symm
      subst R
      simp only [chainMap]
      ring
  | cons I L ih =>
      cases R with
      | nil => simp at hlen
      | cons J R =>
          have ht : L.length = R.length := Nat.succ.inj hlen
          by_cases hx : x ≤ I.right
          · have hy : affine I J x ≤ J.right := by
              rw [← affine_right I J]
              exact (affine_strictMono I J).monotone hx
            simp only [chainMap, if_pos hx, if_pos hy]
            exact affine_inverse I J x
          · have hy : ¬ chainMap b d L R x ≤ J.right := by
              have hm := chainMap_strictMono hL.2 hR.2 ht (lt_of_not_ge hx)
              rw [chainMap_start hL.2 hR.2 ht] at hm
              exact not_le_of_gt hm
            simp only [chainMap, if_neg hx, if_neg hy]
            exact ih hL.2 hR.2 ht

theorem chainMap_on_cells_aux {a b c d : ℝ} {L R : List BasicInterval}
    (hL : GapChain a b L) (hR : GapChain c d R) (hlen : L.length = R.length) :
    List.Forall₂ (fun I J => I ∈ L ∧ ∀ x ∈ I.carrier,
      chainMap b d L R x = affine I J x) L R := by
  induction L generalizing a c R with
  | nil =>
      have hnil : R = [] := List.length_eq_zero_iff.mp hlen.symm
      subst R
      exact List.Forall₂.nil
  | cons I L ih =>
      cases R with
      | nil => simp at hlen
      | cons J R =>
          have ht : L.length = R.length := Nat.succ.inj hlen
          apply List.Forall₂.cons
          · refine ⟨List.mem_cons_self, ?_⟩
            intro x hx
            exact if_pos hx.2
          · apply (ih hL.2 hR.2 ht).imp
            intro K Q hK
            refine ⟨List.mem_cons_of_mem I hK.1, ?_⟩
            intro x hx
            rw [chainMap_eq_tail hL.2 hR.2 ht
              ((hL.2.left_le_of_mem hK.1).trans hx.1)]
            exact hK.2 x hx

theorem chainMap_on_cells {a b c d : ℝ} {L R : List BasicInterval}
    (hL : GapChain a b L) (hR : GapChain c d R) (hlen : L.length = R.length) :
    List.Forall₂ (fun I J => ∀ x ∈ I.carrier,
      chainMap b d L R x = affine I J x) L R :=
  (chainMap_on_cells_aux hL hR hlen).imp (fun _ _ h => h.2)

def intervalOrderIso {L R : List BasicInterval}
    (hL : GapChain 0 1 L) (hR : GapChain 0 1 R) (hlen : L.length = R.length) :
    UnitInterval ≃o UnitInterval where
  toFun x := ⟨chainMap 1 1 L R x, by
    have hm := (chainMap_strictMono hL hR hlen).monotone
    constructor
    · simpa only [chainMap_start hL hR hlen] using hm x.property.1
    · simpa only [chainMap_end hL hR hlen] using hm x.property.2⟩
  invFun x := ⟨chainMap 1 1 R L x, by
    have hm := (chainMap_strictMono hR hL hlen.symm).monotone
    constructor
    · simpa only [chainMap_start hR hL hlen.symm] using hm x.property.1
    · simpa only [chainMap_end hR hL hlen.symm] using hm x.property.2⟩
  left_inv x := Subtype.ext (chainMap_inverse hL hR hlen x)
  right_inv x := Subtype.ext (chainMap_inverse hR hL hlen.symm x)
  map_rel_iff' := (chainMap_strictMono hL hR hlen).le_iff_le

def intervalHomeomorph {L R : List BasicInterval}
    (hL : GapChain 0 1 L) (hR : GapChain 0 1 R) (hlen : L.length = R.length) :
    IntervalHomeomorph := ⟨(intervalOrderIso hL hR hlen).toHomeomorph⟩

theorem intervalHomeomorph_strictMono {L R : List BasicInterval}
    (hL : GapChain 0 1 L) (hR : GapChain 0 1 R) (hlen : L.length = R.length) :
    StrictMono (intervalHomeomorph hL hR hlen) :=
  (intervalOrderIso hL hR hlen).strictMono

def interpolationWitness {L R : List BasicInterval}
    (hL : GapChain 0 1 L) (hR : GapChain 0 1 R) (hlen : L.length = R.length) :
    DyadicPLWitness (intervalHomeomorph hL hR hlen) where
  pieceCount := L.length
  positive := hL.toSubdivision.positive
  knots := hL.toSubdivision.knots
  strictMono_knots := hL.toSubdivision.strictMono_knots
  first := hL.toSubdivision.first
  last := hL.toSubdivision.last
  dyadic := hL.toSubdivision.dyadic
  cover := hL.toSubdivision.cover
  exponent i := ((L.get i).depth : ℤ) - ((R.get (Fin.cast hlen i)).depth : ℤ)
  affine := by
    intro i x hxleft hxright
    let s := hL.toSubdivision
    have hp : ∀ y ∈ (L.get i).carrier, chainMap 1 1 L R y =
        affine (L.get i) (R.get (Fin.cast hlen i)) y :=
      (chainMap_on_cells hL hR hlen).get i.isLt (by simpa only [← hlen] using i.isLt)
    have hx : (x : ℝ) ∈ (L.get i).carrier := by
      constructor
      · rw [← s.left_eq i]
        exact hxleft
      · rw [← s.right_eq i]
        exact hxright
    have hk : (s.knots i.castSucc : ℝ) ∈ (L.get i).carrier := by
      rw [s.left_eq i]
      exact ⟨le_rfl, (L.get i).left_lt_right.le⟩
    change chainMap 1 1 L R (x : ℝ) =
      chainMap 1 1 L R (s.knots i.castSucc : ℝ) +
        (2 : ℝ) ^ (((L.get i).depth : ℤ) - ((R.get (Fin.cast hlen i)).depth : ℤ)) *
          ((x : ℝ) - (s.knots i.castSucc : ℝ))
    rw [hp _ hx, hp _ hk, s.left_eq i, affine_left]
    simp only [affine, affine_slope_zpow]

def transport {L R : List BasicInterval}
    (hL : GapChain 0 1 L) (hR : GapChain 0 1 R) (hlen : L.length = R.length) : F :=
  ⟨intervalHomeomorph hL hR hlen, intervalHomeomorph_strictMono hL hR hlen,
    ⟨interpolationWitness hL hR hlen⟩⟩

theorem transport_on_cells {L R : List BasicInterval}
    (hL : GapChain 0 1 L) (hR : GapChain 0 1 R) (hlen : L.length = R.length) :
    List.Forall₂ (CarriesAffinely (transport hL hR hlen)) L R := by
  apply (chainMap_on_cells hL hR hlen).imp
  intro I J h x
  change chainMap 1 1 L R (I.chart (x : ℝ)) = J.chart (x : ℝ)
  simpa only [BasicInterval.coe_chartPoint, affine_chart] using
    h _ (I.chartPoint_mem_carrier x)

end OrderedPLInterpolation

theorem exists_chain_transport {L R : List BasicInterval}
    (hL : GapChain 0 1 L) (hR : GapChain 0 1 R) (hlen : L.length = R.length) :
    ∃ h : F, List.Forall₂ (CarriesAffinely h) L R :=
  ⟨OrderedPLInterpolation.transport hL hR hlen,
    OrderedPLInterpolation.transport_on_cells hL hR hlen⟩

end ThompsonNonamenability

end

end OAI

end
end

section
section
namespace OAI

/-!
# Simultaneous affine transport of two separated basic intervals

Each of the three complementary gaps is partitioned and equalized separately.
Consequently the selected source and target cells occupy matching positions
in the two full ordered partitions. The interpolation theorem constructs an
actual increasing dyadic PL homeomorphism on those partitions.
-/

noncomputable section


namespace ThompsonNonamenability

private theorem forall₂_after_prefix {α : Type uα} {β : Type uβ} {R : α → β → Prop}
    {A C : List α} {B D : List β} (hlen : A.length = B.length)
    (h : List.Forall₂ R (A ++ C) (B ++ D)) : List.Forall₂ R C D := by
  have hdrop := List.forall₂_drop A.length h
  rw [List.drop_left, hlen, List.drop_left] at hdrop
  exact hdrop

/-- The selected positions are preserved because the three gap lengths are
equalized independently. All partition data will be constructed below. -/
private theorem exists_pair_transport_of_partitions
    (I J I' J' : BasicInterval)
    (P₀ : DyadicGapPartition 0 I.left) (Q₀ : DyadicGapPartition 0 I'.left)
    (P₁ : DyadicGapPartition I.right J.left)
    (Q₁ : DyadicGapPartition I'.right J'.left)
    (P₂ : DyadicGapPartition J.right 1) (Q₂ : DyadicGapPartition J'.right 1)
    (hlen₀ : P₀.cells.length = Q₀.cells.length)
    (hlen₁ : P₁.cells.length = Q₁.cells.length)
    (hlen₂ : P₂.cells.length = Q₂.cells.length) :
    ∃ h : F, CarriesAffinely h I I' ∧ CarriesAffinely h J J' := by
  let L := P₀.cells ++ I :: (P₁.cells ++ J :: P₂.cells)
  let R := Q₀.cells ++ I' :: (Q₁.cells ++ J' :: Q₂.cells)
  have hL : GapChain 0 1 L := by
    exact P₀.chain.append ⟨rfl, P₁.chain.append ⟨rfl, P₂.chain⟩⟩
  have hR : GapChain 0 1 R := by
    exact Q₀.chain.append ⟨rfl, Q₁.chain.append ⟨rfl, Q₂.chain⟩⟩
  have hlen : L.length = R.length := by
    simp only [L, R, List.length_append, List.length_cons, hlen₀, hlen₁, hlen₂]
  obtain ⟨h, hpair⟩ := exists_chain_transport hL hR hlen
  have hpair₀ : List.Forall₂ (CarriesAffinely h)
      (I :: (P₁.cells ++ J :: P₂.cells))
      (I' :: (Q₁.cells ++ J' :: Q₂.cells)) :=
    forall₂_after_prefix hlen₀ hpair
  have hfirst := List.forall₂_cons.mp hpair₀
  have hpair₁ : List.Forall₂ (CarriesAffinely h)
      (J :: P₂.cells) (J' :: Q₂.cells) :=
    forall₂_after_prefix hlen₁ hfirst.2
  exact ⟨h, hfirst.1, (List.forall₂_cons.mp hpair₁).1⟩

/-- Two strictly separated internal basic intervals can simultaneously be
carried onto any other such pair by an actual element of standard Thompson F. -/
theorem exists_affine_pair_transport {I J I' J' : BasicInterval}
    (hI : I.Internal) (hJ : J.Internal)
    (hI' : I'.Internal) (hJ' : J'.Internal)
    (hIJ : I.Before J) (hIJ' : I'.Before J') :
    ∃ h : F, CarriesAffinely h I I' ∧ CarriesAffinely h J J' := by
  obtain ⟨P₀, Q₀, hlen₀⟩ := exists_equal_length_partitions
    isDyadic_zero I.left_isDyadic isDyadic_zero I'.left_isDyadic
    le_rfl (I.left_lt_right.le.trans I.right_le_one)
    le_rfl (I'.left_lt_right.le.trans I'.right_le_one) hI.1 hI'.1
  obtain ⟨P₁, Q₁, hlen₁⟩ := exists_equal_length_partitions
    I.right_isDyadic J.left_isDyadic I'.right_isDyadic J'.left_isDyadic
    (I.left_nonneg.trans I.left_lt_right.le)
    (J.left_lt_right.le.trans J.right_le_one)
    (I'.left_nonneg.trans I'.left_lt_right.le)
    (J'.left_lt_right.le.trans J'.right_le_one) hIJ hIJ'
  obtain ⟨P₂, Q₂, hlen₂⟩ := exists_equal_length_partitions
    J.right_isDyadic isDyadic_one J'.right_isDyadic isDyadic_one
    (J.left_nonneg.trans J.left_lt_right.le) le_rfl
    (J'.left_nonneg.trans J'.left_lt_right.le) le_rfl hJ.2 hJ'.2
  exact exists_pair_transport_of_partitions I J I' J'
    P₀ Q₀ P₁ Q₁ P₂ Q₂ hlen₀ hlen₁ hlen₂

end ThompsonNonamenability

end

end OAI

end
end

section
section
namespace OAI

/-!
# A fixed finite family of actual affine transports

The set of transports depends only on the branching parameter. Each ordered
separated pair in the actual parent/child family is carried onto the reference
pair. After this set is fixed, one partition level is selected for the given
finite group set and all of its translates by these transports.
-/

noncomputable section

open scoped InnerProductSpace


namespace ThompsonNonamenability

local instance : DecidableEq F := Classical.decEq F

variable {D : ℕ}

/-- The ordered separated pairs of actual interval occurrences. -/
def orderedIntervalPairs (D : ℕ) : Finset (IntervalIndex D × IntervalIndex D) := by
  classical
  exact Finset.univ.filter (fun p =>
    (familyInterval D p.1).Before (familyInterval D p.2))

theorem mem_orderedIntervalPairs (D : ℕ) (q r : IntervalIndex D) :
    (q, r) ∈ orderedIntervalPairs D ↔
      (familyInterval D q).Before (familyInterval D r) := by
  classical
  simp only [orderedIntervalPairs, Finset.mem_filter, Finset.mem_univ, true_and]

/-- An actual Thompson-group witness, chosen only for a genuinely separated pair. -/
def pairTransport (hD : 2 ≤ D) (p : {p // p ∈ orderedIntervalPairs D}) : F :=
  Classical.choose (exists_affine_pair_transport
    (familyInterval_internal D p.val.1) (familyInterval_internal D p.val.2)
    (selectedInterval_internal D (firstIndex hD))
    (selectedInterval_internal D (secondIndex hD))
    ((mem_orderedIntervalPairs D p.val.1 p.val.2).mp p.property)
    (reference_before hD))

theorem pairTransport_spec (hD : 2 ≤ D) (p : {p // p ∈ orderedIntervalPairs D}) :
    CarriesAffinely (pairTransport hD p) (familyInterval D p.val.1)
      (familyInterval D (.inl (firstIndex hD))) ∧
    CarriesAffinely (pairTransport hD p) (familyInterval D p.val.2)
      (familyInterval D (.inl (secondIndex hD))) :=
  Classical.choose_spec (exists_affine_pair_transport
    (familyInterval_internal D p.val.1) (familyInterval_internal D p.val.2)
    (selectedInterval_internal D (firstIndex hD))
    (selectedInterval_internal D (secondIndex hD))
    ((mem_orderedIntervalPairs D p.val.1 p.val.2).mp p.property)
    (reference_before hD))

/-- This actual finite subset of F is fixed before any averaging set. -/
def fixedTransportSet (hD : 2 ≤ D) : Finset F :=
  (orderedIntervalPairs D).attach.image (pairTransport hD)

theorem transport_of_before (hD : 2 ≤ D) (q r : IntervalIndex D)
    (hqr : (familyInterval D q).Before (familyInterval D r)) :
    ∃ h ∈ fixedTransportSet hD,
      CarriesAffinely h (familyInterval D q)
        (familyInterval D (.inl (firstIndex hD))) ∧
      CarriesAffinely h (familyInterval D r)
        (familyInterval D (.inl (secondIndex hD))) := by
  let p : {p // p ∈ orderedIntervalPairs D} :=
    ⟨(q, r), (mem_orderedIntervalPairs D q r).mpr hqr⟩
  refine ⟨pairTransport hD p, ?_, pairTransport_spec hD p⟩
  exact Finset.mem_image.mpr ⟨p, Finset.mem_attach _ _, rfl⟩

theorem fixedTransportSet_nonempty (hD : 2 ≤ D) :
    (fixedTransportSet hD).Nonempty := by
  obtain ⟨h, hh, _⟩ := transport_of_before hD
    (.inl (firstIndex hD)) (.inl (secondIndex hD)) (reference_before hD)
  exact ⟨h, hh⟩

/-- The one finite set used to select a common partition level. -/
def transportClosure (S A : Finset F) : Finset F :=
  A ∪ S.biUnion (fun h => leftTranslate h A)

theorem mem_transportClosure_self (S A : Finset F) {g : F} (hg : g ∈ A) :
    g ∈ transportClosure S A := Finset.mem_union_left _ hg

theorem mem_transportClosure_mul (S A : Finset F) {h g : F}
    (hh : h ∈ S) (hg : g ∈ A) : h * g ∈ transportClosure S A := by
  apply Finset.mem_union_right
  exact Finset.mem_biUnion.mpr ⟨h, hh, Finset.mem_image.mpr ⟨g, hg, rfl⟩⟩

/-- A single level works simultaneously on A and on every hA for h in fixed S. -/
theorem exists_transport_admissible (hD : 2 ≤ D) (A : Finset F) :
    ∃ n, (∀ g ∈ A, GlobalAdmissible D n g) ∧
      ∀ h ∈ fixedTransportSet hD, ∀ g ∈ A, GlobalAdmissible D n (h * g) := by
  obtain ⟨n, hn⟩ := exists_common_admissible D
    (transportClosure (fixedTransportSet hD) A)
  exact ⟨n, (fun g hg => hn g (mem_transportClosure_self _ _ hg)),
    fun h hh g hg => hn (h * g) (mem_transportClosure_mul _ _ hh hg)⟩

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Symmetry is used only to orient a separated pair; it introduces no sign
assumption on its real inner product. -/
theorem globalCorrelation_comm (hD : 0 < D) (f : UnitBall E → UnitBall E)
    (n : ℕ) (q r : IntervalIndex D) (g : F) :
    globalCorrelation hD f n q r g = globalCorrelation hD f n r q g := by
  exact real_inner_comm (globalColor hD f n r g : E) (globalColor hD f n q g : E)

/-- All separated correlations are compared with one reference correlation
using only the maximum boundary over the previously fixed finite set. -/
theorem separated_correlation_bound (hD : 2 ≤ D) (f : UnitBall E → UnitBall E)
    (n : ℕ) (A : Finset F) (hA : A.Nonempty)
    (hg : ∀ g ∈ A, GlobalAdmissible D n g)
    (hhg : ∀ h ∈ fixedTransportSet hD, ∀ g ∈ A, GlobalAdmissible D n (h * g))
    (q r : IntervalIndex D)
    (hqr : StrictlySeparated (familyInterval D q) (familyInterval D r)) :
    |realAvg A (globalCorrelation (lt_of_lt_of_le (by decide : 0 < 2) hD) f n q r) -
      realAvg A (globalCorrelation (lt_of_lt_of_le (by decide : 0 < 2) hD) f n
        (.inl (firstIndex hD)) (.inl (secondIndex hD)))| ≤
      boundaryMax (fixedTransportSet hD) (fixedTransportSet_nonempty hD) A := by
  have hDpos : 0 < D := lt_of_lt_of_le (by decide : 0 < 2) hD
  have ordered_bound (u v : IntervalIndex D)
      (huv : (familyInterval D u).Before (familyInterval D v)) :
      |realAvg A (globalCorrelation hDpos f n u v) -
        realAvg A (globalCorrelation hDpos f n
          (.inl (firstIndex hD)) (.inl (secondIndex hD)))| ≤
        boundaryMax (fixedTransportSet hD) (fixedTransportSet_nonempty hD) A := by
    obtain ⟨h, hh, hu, hv⟩ := transport_of_before hD u v huv
    exact (globalCorrelation_translate_bound hDpos f n A hA h u v
      (.inl (firstIndex hD)) (.inl (secondIndex hD)) hu hv hg (hhg h hh)).trans
      (boundaryRatio_le_max _ _ A hh)
  rcases hqr with hqr | hrq
  · exact ordered_bound q r hqr
  · have hsym : realAvg A (globalCorrelation hDpos f n q r) =
        realAvg A (globalCorrelation hDpos f n r q) := by
      exact realAvg_congr A (fun g _ => globalCorrelation_comm hDpos f n q r g)
    rw [hsym]
    exact ordered_bound r q hrq

end ThompsonNonamenability

end

end OAI

end
end

section
section
namespace OAI

/-!
# Displacement forces a lower bound for the finite mean energy

The recursive identities concern the individual vectors, not the image of
their mean under the Lipschitz map. Squared-norm convexity is applied to the
mean of the differences of the images.
-/

open scoped BigOperators


namespace ThompsonNonamenability

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The pointwise inequality obtained from the actual recursive colors. -/
theorem displacement_le_mean_energy {D : ℕ} (hD : 0 < D)
    (f : UnitBall E → UnitBall E) (L δ : ℝ)
    (_hL : 0 < L) (hδ : 0 < δ)
    (hLip : ∀ u v, ‖(f u : E) - f v‖ ≤ L * ‖(u : E) - v‖)
    (hDisp : ∀ u, δ ≤ ‖(f u : E) - u‖)
    (x z : Fin D → UnitBall E) (hrec : ∀ i, x i = f (z i)) :
    δ ^ 2 ≤ L ^ 2 * (D : ℝ)⁻¹ *
      ∑ i, ‖(z i : E) - (ballMean hD x : E)‖ ^ 2 := by
  have hxmean : finMean (fun i => (f (z i) : E)) = (ballMean hD x : E) := by
    rw [coe_ballMean]
    apply congrArg finMean
    funext i
    exact congrArg Subtype.val (hrec i).symm
  have hmean : finMean (fun i => (f (z i) : E) - (f (ballMean hD x) : E)) =
      (ballMean hD x : E) - (f (ballMean hD x) : E) := by
    rw [finMean_sub, finMean_const hD, hxmean]
  have hdis : δ ≤ ‖(ballMean hD x : E) - (f (ballMean hD x) : E)‖ := by
    calc
      δ ≤ ‖(f (ballMean hD x) : E) - (ballMean hD x : E)‖ := hDisp _
      _ = ‖(ballMean hD x : E) - (f (ballMean hD x) : E)‖ := norm_sub_rev _ _
  have hlip_sq (i : Fin D) :
      ‖(f (z i) : E) - (f (ballMean hD x) : E)‖ ^ 2 ≤
        L ^ 2 * ‖(z i : E) - (ballMean hD x : E)‖ ^ 2 := by
    calc
      _ ≤ (L * ‖(z i : E) - (ballMean hD x : E)‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (hLip (z i) (ballMean hD x)) 2
      _ = _ := mul_pow _ _ _
  have hjensen := norm_finMean_sq_le hD
    (fun i => (f (z i) : E) - (f (ballMean hD x) : E))
  rw [hmean] at hjensen
  calc
    δ ^ 2 ≤ ‖(ballMean hD x : E) - (f (ballMean hD x) : E)‖ ^ 2 :=
      pow_le_pow_left₀ hδ.le hdis 2
    _ ≤ (D : ℝ)⁻¹ * ∑ i,
        ‖(f (z i) : E) - (f (ballMean hD x) : E)‖ ^ 2 := hjensen
    _ ≤ (D : ℝ)⁻¹ * ∑ i,
        L ^ 2 * ‖(z i : E) - (ballMean hD x : E)‖ ^ 2 :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => hlip_sq i))
        (inv_nonneg.mpr (Nat.cast_nonneg D))
    _ = L ^ 2 * (D : ℝ)⁻¹ *
        ∑ i, ‖(z i : E) - (ballMean hD x : E)‖ ^ 2 := by
      rw [← Finset.mul_sum]
      ring

end ThompsonNonamenability

end OAI

end
end

section
section
namespace OAI

/-!
# The exact positive constant in the finite boundary obstruction

The energy inequality is rearranged only after proving the denominators
positive. No sign condition is imposed on a correlation or on its error bound.
The choice of the integer parameter is independent of the finite group set.
-/

namespace ThompsonNonamenability

noncomputable def boundaryConstant (L δ : ℝ) (D : ℕ) : ℝ :=
  (δ ^ 2 / L ^ 2 - 4 / (D : ℝ)) / (4 * (1 - 1 / (D : ℝ)))

theorem boundary_denominator_pos {D : ℕ} (hD : 2 ≤ D) :
    0 < 4 * (1 - 1 / (D : ℝ)) := by
  have htwo : (2 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD
  have hpos : (0 : ℝ) < (D : ℝ) := by linarith
  have hinv : 1 / (D : ℝ) < 1 := (div_lt_one hpos).2 (by linarith)
  linarith

theorem boundary_numerator_pos {L δ : ℝ} {D : ℕ}
    (hL : 0 < L) (hδ : 0 < δ) (hD : 2 ≤ D)
    (hlarge : 4 * L ^ 2 / δ ^ 2 < (D : ℝ)) :
    0 < δ ^ 2 / L ^ 2 - 4 / (D : ℝ) := by
  have hLp : 0 < L ^ 2 := sq_pos_of_pos hL
  have hδp : 0 < δ ^ 2 := sq_pos_of_pos hδ
  have hDp : (0 : ℝ) < (D : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) hD)
  have hcross : 4 * L ^ 2 < (D : ℝ) * δ ^ 2 :=
    (div_lt_iff₀ hδp).1 hlarge
  have hratio : 4 / (D : ℝ) < δ ^ 2 / L ^ 2 :=
    (div_lt_div_iff₀ hDp hLp).2 (by nlinarith [hcross])
  exact sub_pos.mpr hratio

theorem boundaryConstant_pos {L δ : ℝ} {D : ℕ}
    (hL : 0 < L) (hδ : 0 < δ) (hD : 2 ≤ D)
    (hlarge : 4 * L ^ 2 / δ ^ 2 < (D : ℝ)) :
    0 < boundaryConstant L δ D := by
  unfold boundaryConstant
  exact div_pos (boundary_numerator_pos hL hδ hD hlarge)
    (boundary_denominator_pos hD)

/-- Algebraic consequence of the genuine finite energy estimate. -/
theorem boundaryConstant_le_of_energy {L δ η : ℝ} {D : ℕ}
    (hL : 0 < L) (hD : 2 ≤ D)
    (henergy : δ ^ 2 ≤ L ^ 2 *
      (4 / (D : ℝ) + 4 * (1 - 1 / (D : ℝ)) * η)) :
    boundaryConstant L δ D ≤ η := by
  have hLp : 0 < L ^ 2 := sq_pos_of_pos hL
  have hdivide : δ ^ 2 / L ^ 2 ≤
      4 / (D : ℝ) + 4 * (1 - 1 / (D : ℝ)) * η := by
    apply (div_le_iff₀ hLp).2
    nlinarith [henergy]
  unfold boundaryConstant
  apply (div_le_iff₀ (boundary_denominator_pos hD)).2
  nlinarith [hdivide]

/-- Choose the finite branching parameter before choosing any finite group set. -/
theorem exists_branching_parameter (L δ : ℝ) :
    ∃ D : ℕ, 2 ≤ D ∧ 4 * L ^ 2 / δ ^ 2 < (D : ℝ) := by
  obtain ⟨n, hn⟩ := exists_nat_gt (4 * L ^ 2 / δ ^ 2)
  refine ⟨max 2 n, le_max_left _ _, lt_of_lt_of_le hn ?_⟩
  exact_mod_cast (le_max_right 2 n)

end ThompsonNonamenability

end OAI

end
end

section
section
namespace OAI

/-!
# From the actual recursive vectors and correlations to a boundary bound

This finite analytic bridge averages the pointwise displacement estimate and
uses the exact correlation variance theorem. Its intermediate hypotheses are
later supplied by the actual dyadic coloring and affine transports.
-/

noncomputable section

open scoped BigOperators InnerProductSpace


namespace ThompsonNonamenability

variable {G : Type uG} {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {D : ℕ}

theorem finite_energy_of_variance (A : Finset G) (hA : A.Nonempty) (hD : 0 < D)
    (f : UnitBall E → UnitBall E) (L δ V : ℝ) (hL : 0 < L) (hδ : 0 < δ)
    (hLip : ∀ u v, ‖(f u : E) - f v‖ ≤ L * ‖(u : E) - v‖)
    (hDisp : ∀ u, δ ≤ ‖(f u : E) - u‖)
    (x z : G → Fin D → UnitBall E)
    (hrec : ∀ g ∈ A, ∀ i, x g i = f (z g i))
    (hvar : ∀ i, realAvg A
      (fun g => ‖(z g i : E) - (ballMean hD (x g) : E)‖ ^ 2) ≤ V) :
    δ ^ 2 ≤ L ^ 2 * V := by
  have havg := const_le_realAvg A hA (fun g hg =>
    displacement_le_mean_energy hD f L δ hL hδ hLip hDisp (x g) (z g) (hrec g hg))
  rw [realAvg_const_mul, realAvg_sum_univ] at havg
  have hsum : (∑ i, realAvg A
      (fun g => ‖(z g i : E) - (ballMean hD (x g) : E)‖ ^ 2)) ≤ (D : ℝ) * V := by
    calc
      _ ≤ ∑ _i : Fin D, V := Finset.sum_le_sum (fun i _ => hvar i)
      _ = (D : ℝ) * V := by simp [nsmul_eq_mul]
  have hfactor : 0 ≤ L ^ 2 * (D : ℝ)⁻¹ :=
    mul_nonneg (sq_nonneg L) (inv_nonneg.mpr (Nat.cast_nonneg D))
  have hDn : (D : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hD)
  calc
    δ ^ 2 ≤ (L ^ 2 * (D : ℝ)⁻¹) * ∑ i, realAvg A
        (fun g => ‖(z g i : E) - (ballMean hD (x g) : E)‖ ^ 2) := havg
    _ ≤ (L ^ 2 * (D : ℝ)⁻¹) * ((D : ℝ) * V) :=
      mul_le_mul_of_nonneg_left hsum hfactor
    _ = L ^ 2 * V := by
      field_simp [hDn]

theorem boundaryConstant_le_of_correlations (A : Finset G) (hA : A.Nonempty)
    (hD : 2 ≤ D) (f : UnitBall E → UnitBall E) (L δ α η : ℝ)
    (hL : 0 < L) (hδ : 0 < δ)
    (hLip : ∀ u v, ‖(f u : E) - f v‖ ≤ L * ‖(u : E) - v‖)
    (hDisp : ∀ u, δ ≤ ‖(f u : E) - u‖)
    (x : G → Fin D → UnitBall E) (y : G → Fin D → Fin D → UnitBall E)
    (hrec : ∀ g ∈ A, ∀ i,
      x g i = f (ballMean (lt_of_lt_of_le (by decide : 0 < 2) hD) (y g i)))
    (hparent : ∀ j k, j ≠ k →
      |corr A (fun g => (x g j : E)) (fun g => (x g k : E)) - α| ≤ η)
    (hchild : ∀ i j k, j ≠ k →
      |corr A (fun g => (y g i j : E)) (fun g => (y g i k : E)) - α| ≤ η)
    (hmixed : ∀ i j k, k ≠ i →
      |corr A (fun g => (y g i j : E)) (fun g => (x g k : E)) - α| ≤ η) :
    boundaryConstant L δ D ≤ η := by
  have hDpos : 0 < D := lt_of_lt_of_le (by decide : 0 < 2) hD
  have hvar := finite_variance_bound A hA hDpos
    (fun g i => (x g i : E)) (fun g i j => (y g i j : E)) α η
    (fun g _ i => (x g i).property) (fun g _ i j => (y g i j).property)
    hparent hchild hmixed
  have henergy := finite_energy_of_variance A hA hDpos f L δ
    (4 / (D : ℝ) + 4 * (1 - 1 / (D : ℝ)) * η) hL hδ hLip hDisp x
    (fun g i => ballMean hDpos (y g i)) hrec (by
      intro i
      simpa only [coe_ballMean] using hvar i)
  exact boundaryConstant_le_of_energy hL hD henergy

end ThompsonNonamenability

end

end OAI

end
end

section
section
namespace OAI

noncomputable section


namespace ThompsonNonamenability

local instance : DecidableEq F := Classical.decEq F

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem exists_fixed_boundary (f : UnitBall E → UnitBall E) (L δ : ℝ)
    (hL : 0 < L) (hδ : 0 < δ)
    (hLip : ∀ x y, ‖(f x : E) - f y‖ ≤ L * ‖(x : E) - y‖)
    (hDisp : ∀ x, δ ≤ ‖(f x : E) - x‖)
    (D : ℕ) (hD : 2 ≤ D) (hlarge : 4 * L ^ 2 / δ ^ 2 < (D : ℝ)) :
    ∃ S : Finset F, S.Nonempty ∧ 0 < boundaryConstant L δ D ∧
      ∀ A : Finset F, A.Nonempty →
        ∃ h ∈ S, boundaryConstant L δ D ≤ boundaryRatio A h := by
  refine ⟨fixedTransportSet hD, fixedTransportSet_nonempty hD,
    boundaryConstant_pos hL hδ hD hlarge, ?_⟩
  intro A hA
  obtain ⟨n, hg, hhg⟩ := exists_transport_admissible hD A
  have hDpos : 0 < D := lt_of_lt_of_le (by decide : 0 < 2) hD
  let x : F → Fin D → UnitBall E := fun g i => globalColor hDpos f n (.inl i) g
  let y : F → Fin D → Fin D → UnitBall E :=
    fun g i j => globalColor hDpos f n (.inr (i, j)) g
  let α : ℝ := realAvg A (globalCorrelation hDpos f n
    (.inl (firstIndex hD)) (.inl (secondIndex hD)))
  let η : ℝ := boundaryMax (fixedTransportSet hD) (fixedTransportSet_nonempty hD) A
  have hrec : ∀ g ∈ A, ∀ i, x g i = f (ballMean hDpos (y g i)) := by
    intro g hmem i
    exact globalColor_parent hDpos f n g (hg g hmem) i
  have hparent : ∀ j k, j ≠ k →
      |corr A (fun g => (x g j : E)) (fun g => (x g k : E)) - α| ≤ η := by
    intro j k hjk
    exact separated_correlation_bound hD f n A hA hg hhg (.inl j) (.inl k)
      (selectedInterval_separated hjk)
  have hchild : ∀ i j k, j ≠ k →
      |corr A (fun g => (y g i j : E)) (fun g => (y g i k : E)) - α| ≤ η := by
    intro i j k hjk
    exact separated_correlation_bound hD f n A hA hg hhg (.inr (i, j)) (.inr (i, k))
      (selected_siblings_separated i hjk)
  have hmixed : ∀ i j k, k ≠ i →
      |corr A (fun g => (y g i j : E)) (fun g => (x g k : E)) - α| ≤ η := by
    intro i j k hki
    exact separated_correlation_bound hD f n A hA hg hhg (.inr (i, j)) (.inl k)
      (selected_child_parent_separated i j k hki)
  have hb : boundaryConstant L δ D ≤ η :=
    boundaryConstant_le_of_correlations A hA hD f L δ α η hL hδ hLip hDisp
      x y hrec hparent hchild hmixed
  exact exists_boundary_ge_of_le_max (fixedTransportSet hD)
    (fixedTransportSet_nonempty hD) A hb

end ThompsonNonamenability

end

end OAI

end
end

section
section
namespace OAI

noncomputable section

namespace ThompsonNonamenability.Analytic

open MeasureTheory Set

abbrev Plane := EuclideanSpace ℝ (Fin 2)

abbrev intervalMeasure : Measure ℝ := volume.restrict (Icc (0 : ℝ) 1)

abbrev Hilbert := Lp Plane 2 intervalMeasure

abbrev Ball := UnitBall Hilbert

end ThompsonNonamenability.Analytic

end

end OAI

end
end

section
section
namespace OAI

/-!
# The Euclidean planar oscillator

The ordinary sine/cosine circle and its tangent have unit Euclidean norm.
The derivative of the tangent is the negative circle vector. The mean value
inequality therefore gives Lipschitz constant one for both functions, and a
quadratic first-order remainder estimate with constant one.
-/

noncomputable section

namespace ThompsonNonamenability.Analytic

open Set
open scoped InnerProductSpace

def planeWave (z : ℝ) : Plane := !₂[Real.cos z, Real.sin z]

def planeDeriv (z : ℝ) : Plane := !₂[-Real.sin z, Real.cos z]

@[simp] theorem planeWave_norm (z : ℝ) : ‖planeWave z‖ = 1 := by
  simp [planeWave, EuclideanSpace.norm_eq, Fin.sum_univ_two,
    Real.norm_eq_abs, sq_abs, Real.cos_sq_add_sin_sq]

@[simp] theorem planeDeriv_norm (z : ℝ) : ‖planeDeriv z‖ = 1 := by
  simp [planeDeriv, EuclideanSpace.norm_eq, Fin.sum_univ_two,
    Real.norm_eq_abs, sq_abs, Real.sin_sq_add_cos_sq]

theorem planeWave_inner_planeDeriv (z : ℝ) :
    ⟪planeWave z, planeDeriv z⟫_ℝ = 0 := by
  simp [planeWave, planeDeriv, PiLp.inner_apply, Fin.sum_univ_two,
    RCLike.inner_apply, mul_comm]

theorem planeWave_inner (s t : ℝ) :
    ⟪planeWave s, planeWave t⟫_ℝ = Real.cos (t - s) := by
  simp [planeWave, PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply,
    Real.cos_sub]

private theorem hasDerivAt_planePair {f g : ℝ → ℝ} {f' g' z : ℝ}
    (hf : HasDerivAt f f' z) (hg : HasDerivAt g g' z) :
    HasDerivAt (fun x => (!₂[f x, g x] : Plane)) (!₂[f', g'] : Plane) z := by
  have h : HasDerivAt (fun x => (![f x, g x] : Fin 2 → ℝ)) ![f', g'] z := by
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · simpa using hf
    · simpa using hg
  exact (EuclideanSpace.equiv (Fin 2) ℝ).symm.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt z h

theorem hasDerivAt_planeWave (z : ℝ) :
    HasDerivAt planeWave (planeDeriv z) z :=
  hasDerivAt_planePair (Real.hasDerivAt_cos z) (Real.hasDerivAt_sin z)

theorem hasDerivAt_planeDeriv (z : ℝ) :
    HasDerivAt planeDeriv (-planeWave z) z := by
  have h := hasDerivAt_planePair (Real.hasDerivAt_sin z).neg (Real.hasDerivAt_cos z)
  have he : (!₂[-Real.cos z, -Real.sin z] : Plane) = -planeWave z := by
    ext i
    fin_cases i <;> simp [planeWave]
  rw [he] at h
  exact h

theorem continuous_planeWave : Continuous planeWave :=
  Differentiable.continuous (fun z => (hasDerivAt_planeWave z).differentiableAt)

theorem continuous_planeDeriv : Continuous planeDeriv :=
  Differentiable.continuous (fun z => (hasDerivAt_planeDeriv z).differentiableAt)

theorem planeWave_sub_norm_le (s t : ℝ) :
    ‖planeWave s - planeWave t‖ ≤ |s - t| := by
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := planeWave) (f' := planeDeriv) (C := 1)
    (fun x (_ : x ∈ (Set.univ : Set ℝ)) =>
      (hasDerivAt_planeWave x).hasDerivWithinAt)
    (fun x _ => le_of_eq (planeDeriv_norm x)) convex_univ (mem_univ t) (mem_univ s)
  simpa only [one_mul, Real.norm_eq_abs] using h

theorem planeDeriv_sub_norm_le (s t : ℝ) :
    ‖planeDeriv s - planeDeriv t‖ ≤ |s - t| := by
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := planeDeriv) (f' := fun x => -planeWave x) (C := 1)
    (fun x (_ : x ∈ (Set.univ : Set ℝ)) =>
      (hasDerivAt_planeDeriv x).hasDerivWithinAt)
    (fun x _ => by simp) convex_univ (mem_univ t) (mem_univ s)
  simpa only [one_mul, Real.norm_eq_abs] using h

theorem planeWave_remainder (s t : ℝ) :
    ‖planeWave t - planeWave s - (t - s) • planeDeriv s‖ ≤ |t - s| ^ 2 := by
  have hd (x : ℝ) :
      HasDerivAt (fun y => planeWave y - planeWave s - (y - s) • planeDeriv s)
        (planeDeriv x - planeDeriv s) x := by
    simpa only [one_smul, id_eq] using
      ((hasDerivAt_planeWave x).sub_const (planeWave s)).fun_sub
        (((hasDerivAt_id x).sub_const s).smul_const (planeDeriv s))
  have hbound (x : ℝ) (hx : x ∈ segment ℝ s t) :
      ‖planeDeriv x - planeDeriv s‖ ≤ |t - s| := by
    apply (planeDeriv_sub_norm_le x s).trans
    simpa only [Real.norm_eq_abs] using norm_sub_le_of_mem_segment hx
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun x (_ : x ∈ segment ℝ s t) => (hd x).hasDerivWithinAt)
    hbound (convex_segment s t) (left_mem_segment ℝ s t) (right_mem_segment ℝ s t)
  simpa only [sub_self, zero_smul, sub_zero, Real.norm_eq_abs, pow_two] using h

end ThompsonNonamenability.Analytic

end

end OAI

end
end

section
section
namespace OAI

/-!
# Uniform estimates in the concrete Hilbert space

The restricted Lebesgue measure has mass one. Consequently, an almost-everywhere
uniform bound on a representative gives the same bound on its `L²` norm.
The derivative criterion below turns a quadratic norm remainder into a genuine
derivative in any real normed space, including this Hilbert space.
-/

noncomputable section


namespace ThompsonNonamenability.Analytic

open MeasureTheory Set Filter
open scoped Topology Asymptotics ENNReal

@[simp] theorem intervalMeasure_univ : intervalMeasure univ = 1 := by
  simp [intervalMeasure, Real.volume_Icc]

/-- A uniform bound on an almost-everywhere representative bounds the Hilbert norm. -/
theorem norm_le_of_ae_bound (f : Hilbert) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ᵐ x ∂intervalMeasure, ‖f x‖ ≤ C) : ‖f‖ ≤ C := by
  rw [Lp.norm_def]
  have h : eLpNorm f 2 intervalMeasure ≤ ENNReal.ofReal C := by
    simpa only [intervalMeasure_univ, ENNReal.one_rpow, one_mul] using
      (eLpNorm_le_of_ae_bound (p := (2 : ℝ≥0∞)) hbound)
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top h).trans_eq
    (ENNReal.toReal_ofReal hC)

/-- A quadratic norm remainder implies differentiability, without any pointwise
choice of representatives in the codomain. -/
theorem hasDerivAt_of_quadratic_remainder
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} {f' : E} {x C : ℝ}
    (hrem : ∀ᶠ h in 𝓝 (0 : ℝ),
      ‖f (x + h) - f x - h • f'‖ ≤ C * |h| ^ 2) :
    HasDerivAt f f' x := by
  apply hasDerivAt_iff_isLittleO_nhds_zero.mpr
  have hO :
      (fun h : ℝ => f (x + h) - f x - h • f') =O[𝓝 0]
        (fun h : ℝ => h ^ 2) := by
    apply Asymptotics.IsBigO.of_bound C
    simpa only [norm_pow, Real.norm_eq_abs] using hrem
  exact hO.trans_isLittleO
    (Asymptotics.isLittleO_pow_id (n := 2) (by decide))

end ThompsonNonamenability.Analytic

end

end OAI

end
end

section
section
namespace OAI

/-!
# The correlation function for the Hilbert-space oscillator

The value at zero is filled in by the derivative of sine. Uniform separation
on a positive half-line is proved using one compact interval and the elementary
bound on sine, without a limit argument at infinity.
-/

noncomputable section

namespace ThompsonNonamenability.Analytic

open Set

def sinc (q : ℝ) : ℝ := if q = 0 then 1 else Real.sin q / q

@[simp] theorem sinc_zero : sinc 0 = 1 := by simp [sinc]

theorem sinc_of_ne_zero {q : ℝ} (hq : q ≠ 0) : sinc q = Real.sin q / q := by
  simp [sinc, hq]

@[simp] theorem sinc_neg (q : ℝ) : sinc (-q) = sinc q := by
  by_cases hq : q = 0
  · simp [hq]
  · simp [sinc, hq, Real.sin_neg]

private theorem sinc_eq_update :
    sinc = Function.update (fun q : ℝ => Real.sin q / q) 0 1 := by
  funext q
  by_cases hq : q = 0 <;> simp [sinc, hq]

theorem continuous_sinc : Continuous sinc := by
  rw [continuous_iff_continuousAt]
  intro q
  rw [sinc_eq_update]
  by_cases hq : q = 0
  · subst q
    simpa only [Real.sin_zero, Real.cos_zero, sub_zero] using
      (Real.hasDerivAt_sin 0).continuousAt_div
  · exact (continuousAt_update_of_ne hq).2
      (Real.continuous_sin.continuousAt.div continuousAt_id hq)

theorem abs_sinc_lt_one {q : ℝ} (hq : q ≠ 0) : |sinc q| < 1 := by
  rw [sinc_of_ne_zero hq, abs_div]
  exact (div_lt_one (abs_pos.mpr hq)).2 (Real.abs_sin_lt_abs hq)

theorem abs_sinc_le_half_of_two_le {q : ℝ} (hq : 2 ≤ q) : |sinc q| ≤ 1 / 2 := by
  have hqpos : 0 < q := by linarith
  rw [sinc_of_ne_zero (ne_of_gt hqpos), abs_div, abs_of_pos hqpos]
  apply (div_le_iff₀ hqpos).2
  nlinarith [Real.abs_sin_le_one q]

theorem exists_uniform_sinc_gap (d : ℝ) (hd : 0 < d) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 / 2 ∧
      ∀ q : ℝ, d ≤ q → ε ≤ 1 - sinc q := by
  have hdmin : 0 < min d 1 := lt_min hd (by norm_num)
  have hpositive : ∀ q ∈ Icc (min d 1) 2, 0 < 1 - sinc q := by
    intro q hq
    have hqpos : 0 < q := hdmin.trans_le hq.1
    have hs : sinc q < 1 :=
      (le_abs_self _).trans_lt (abs_sinc_lt_one (ne_of_gt hqpos))
    linarith
  obtain ⟨m, hm, hbound⟩ :=
    (isCompact_Icc : IsCompact (Icc (min d 1) (2 : ℝ))).exists_forall_le'
      (continuous_const.sub continuous_sinc).continuousOn hpositive
  refine ⟨min m (1 / 2), lt_min hm (by norm_num), min_le_right _ _, ?_⟩
  intro q hq
  by_cases hq2 : q ≤ 2
  · exact (min_le_left _ _).trans
      (hbound q ⟨(min_le_left d 1).trans hq, hq2⟩)
  · have hs : sinc q ≤ 1 / 2 :=
      (le_abs_self _).trans (abs_sinc_le_half_of_two_le (le_of_not_ge hq2))
    have hhalf : (1 / 2 : ℝ) ≤ 1 - sinc q := by linarith
    exact (min_le_right _ _).trans hhalf

end ThompsonNonamenability.Analytic

end

end OAI

end
end

section
section
namespace OAI

/-!
# The concrete square-integrable oscillator

The representatives are `(cos (z*w), sin (z*w))` and its parameter
derivative `w * (-sin (z*w), cos (z*w))`.  Every passage from a
representative to an `Lp` element uses an almost-everywhere equality.
-/

noncomputable section

namespace ThompsonNonamenability.Analytic

open MeasureTheory Set Filter
open scoped Topology

def waveRep (z w : ℝ) : Plane := planeWave (z * w)

def waveDerivRep (z w : ℝ) : Plane := w • planeDeriv (z * w)

theorem continuous_waveRep (z : ℝ) : Continuous (waveRep z) :=
  continuous_planeWave.comp (continuous_const.mul continuous_id)

theorem continuous_waveDerivRep (z : ℝ) : Continuous (waveDerivRep z) :=
  continuous_id.smul
    (continuous_planeDeriv.comp (continuous_const.mul continuous_id))

theorem waveRep_norm (z w : ℝ) : ‖waveRep z w‖ = 1 :=
  planeWave_norm _

theorem waveDerivRep_norm (z w : ℝ) : ‖waveDerivRep z w‖ = |w| := by
  simp [waveDerivRep, norm_smul, planeDeriv_norm, Real.norm_eq_abs]

theorem waveRep_memLp (z : ℝ) : MemLp (waveRep z) 2 intervalMeasure := by
  apply MemLp.of_bound (continuous_waveRep z).aestronglyMeasurable 1
  exact ae_of_all _ fun w => le_of_eq (waveRep_norm z w)

theorem waveDerivRep_memLp (z : ℝ) : MemLp (waveDerivRep z) 2 intervalMeasure := by
  apply MemLp.of_bound (continuous_waveDerivRep z).aestronglyMeasurable 1
  filter_upwards [ae_restrict_mem measurableSet_Icc] with w hw
  rw [waveDerivRep_norm, abs_of_nonneg hw.1]
  exact hw.2

/-- The oscillator as an actual equivalence class in `L²([0,1]; ℝ²)`. -/
def wave (z : ℝ) : Hilbert := (waveRep_memLp z).toLp (waveRep z)

/-- The proposed derivative, independently defined from its concrete representative. -/
def waveDeriv (z : ℝ) : Hilbert :=
  (waveDerivRep_memLp z).toLp (waveDerivRep z)

theorem wave_coeFn (z : ℝ) : ⇑(wave z) =ᵐ[intervalMeasure] waveRep z :=
  (waveRep_memLp z).coeFn_toLp

theorem waveDeriv_coeFn (z : ℝ) : ⇑(waveDeriv z) =ᵐ[intervalMeasure] waveDerivRep z :=
  (waveDerivRep_memLp z).coeFn_toLp

theorem integral_intervalMeasure (f : ℝ → ℝ) :
    (∫ w, f w ∂intervalMeasure) = ∫ w in (0 : ℝ)..1, f w := by
  change (∫ w in Icc (0 : ℝ) 1, f w) = _
  rw [integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le (by norm_num)]

theorem integral_cos_intervalMeasure (q : ℝ) :
    (∫ w, Real.cos (q * w) ∂intervalMeasure) = sinc q := by
  rw [integral_intervalMeasure]
  by_cases hq : q = 0
  · simp [hq, sinc_zero]
  · rw [sinc_of_ne_zero hq, intervalIntegral.integral_comp_mul_left _ hq,
      _root_.integral_cos]
    simp [div_eq_mul_inv, mul_comm]

theorem wave_inner (s t : ℝ) : inner (𝕜 := ℝ) (wave s) (wave t) = sinc (t - s) := by
  rw [L2.inner_def]
  calc
    (∫ w, inner (𝕜 := ℝ) (wave s w) (wave t w) ∂intervalMeasure) =
        ∫ w, Real.cos ((t - s) * w) ∂intervalMeasure := by
      apply integral_congr_ae
      filter_upwards [wave_coeFn s, wave_coeFn t] with w hs ht
      rw [hs, ht]
      change inner (𝕜 := ℝ) (planeWave (s * w)) (planeWave (t * w)) =
        Real.cos ((t - s) * w)
      rw [planeWave_inner]
      congr 1
      ring
    _ = sinc (t - s) := integral_cos_intervalMeasure _

theorem wave_norm (z : ℝ) : ‖wave z‖ = 1 := by
  have h := wave_inner z z
  rw [real_inner_self_eq_norm_sq] at h
  simp only [sub_self, sinc_zero] at h
  nlinarith [norm_nonneg (wave z)]

theorem waveDeriv_norm_sq (z : ℝ) : ‖waveDeriv z‖ ^ 2 = 1 / 3 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  calc
    (∫ w, inner (𝕜 := ℝ) (waveDeriv z w) (waveDeriv z w) ∂intervalMeasure) =
        ∫ w, w ^ 2 ∂intervalMeasure := by
      apply integral_congr_ae
      filter_upwards [waveDeriv_coeFn z] with w hw
      rw [hw, real_inner_self_eq_norm_sq, waveDerivRep_norm, sq_abs]
    _ = 1 / 3 := by rw [integral_intervalMeasure, _root_.integral_pow]; norm_num

theorem wave_inner_waveDeriv (z : ℝ) : inner (𝕜 := ℝ) (wave z) (waveDeriv z) = 0 := by
  rw [L2.inner_def]
  calc
    (∫ w, inner (𝕜 := ℝ) (wave z w) (waveDeriv z w) ∂intervalMeasure) =
        ∫ _w : ℝ, (0 : ℝ) ∂intervalMeasure := by
      apply integral_congr_ae
      filter_upwards [wave_coeFn z, waveDeriv_coeFn z] with w hw hd
      rw [hw, hd]
      change inner (𝕜 := ℝ) (planeWave (z * w)) (w • planeDeriv (z * w)) = 0
      rw [real_inner_smul_right, planeWave_inner_planeDeriv, mul_zero]
    _ = 0 := integral_zero _ _

theorem waveRep_sub_norm_le (s t w : ℝ) (hw : w ∈ Icc (0 : ℝ) 1) :
    ‖waveRep s w - waveRep t w‖ ≤ |s - t| := by
  calc
    ‖waveRep s w - waveRep t w‖ ≤ |s * w - t * w| :=
      planeWave_sub_norm_le _ _
    _ = |s - t| * w := by rw [← sub_mul, abs_mul, abs_of_nonneg hw.1]
    _ ≤ |s - t| := mul_le_of_le_one_right (abs_nonneg _) hw.2

theorem waveDerivRep_sub_norm_le (s t w : ℝ) (hw : w ∈ Icc (0 : ℝ) 1) :
    ‖waveDerivRep s w - waveDerivRep t w‖ ≤ |s - t| := by
  have hw2 : w * w ≤ 1 := (mul_le_of_le_one_right hw.1 hw.2).trans hw.2
  calc
    ‖waveDerivRep s w - waveDerivRep t w‖ =
        w * ‖planeDeriv (s * w) - planeDeriv (t * w)‖ := by
      rw [waveDerivRep, waveDerivRep, ← smul_sub, norm_smul,
        Real.norm_eq_abs, abs_of_nonneg hw.1]
    _ ≤ w * |s * w - t * w| :=
      mul_le_mul_of_nonneg_left (planeDeriv_sub_norm_le _ _) hw.1
    _ = |s - t| * (w * w) := by
      rw [← sub_mul, abs_mul, abs_of_nonneg hw.1]
      ring
    _ ≤ |s - t| := mul_le_of_le_one_right (abs_nonneg _) hw2

theorem wave_sub_norm_le (s t : ℝ) : ‖wave s - wave t‖ ≤ |s - t| := by
  apply norm_le_of_ae_bound _ (abs_nonneg _)
  filter_upwards [Lp.coeFn_sub (wave s) (wave t), wave_coeFn s, wave_coeFn t,
    ae_restrict_mem measurableSet_Icc] with w hsub hs ht hw
  simpa only [hsub, Pi.sub_apply, hs, ht] using waveRep_sub_norm_le s t w hw

theorem waveDeriv_sub_norm_le (s t : ℝ) :
    ‖waveDeriv s - waveDeriv t‖ ≤ |s - t| := by
  apply norm_le_of_ae_bound _ (abs_nonneg _)
  filter_upwards [Lp.coeFn_sub (waveDeriv s) (waveDeriv t), waveDeriv_coeFn s,
    waveDeriv_coeFn t, ae_restrict_mem measurableSet_Icc] with w hsub hs ht hw
  simpa only [hsub, Pi.sub_apply, hs, ht] using waveDerivRep_sub_norm_le s t w hw

theorem waveRep_remainder (z h w : ℝ) (hw : w ∈ Icc (0 : ℝ) 1) :
    ‖waveRep (z + h) w - waveRep z w - h • waveDerivRep z w‖ ≤ |h| ^ 2 := by
  have hscalar : (z + h) * w - z * w = h * w := by ring
  have hrem := planeWave_remainder (z * w) ((z + h) * w)
  rw [hscalar] at hrem
  have hw2 : w ^ 2 ≤ 1 := by nlinarith [mul_nonneg hw.1 (sub_nonneg.mpr hw.2)]
  calc
    ‖waveRep (z + h) w - waveRep z w - h • waveDerivRep z w‖ =
        ‖planeWave ((z + h) * w) - planeWave (z * w) -
          (h * w) • planeDeriv (z * w)‖ := by
      simp only [waveRep, waveDerivRep, mul_smul]
    _ ≤ |h * w| ^ 2 := hrem
    _ = |h| ^ 2 * w ^ 2 := by simp only [abs_mul, mul_pow, sq_abs]
    _ ≤ |h| ^ 2 := mul_le_of_le_one_right (sq_nonneg _) hw2

theorem wave_remainder (z h : ℝ) :
    ‖wave (z + h) - wave z - h • waveDeriv z‖ ≤ |h| ^ 2 := by
  apply norm_le_of_ae_bound _ (sq_nonneg _)
  filter_upwards
    [Lp.coeFn_sub (wave (z + h) - wave z) (h • waveDeriv z),
      Lp.coeFn_sub (wave (z + h)) (wave z), Lp.coeFn_smul h (waveDeriv z),
      wave_coeFn (z + h), wave_coeFn z, waveDeriv_coeFn z,
      ae_restrict_mem measurableSet_Icc] with w ho hi hm hh hz hd hw
  simpa only [ho, hi, hm, Pi.sub_apply, Pi.smul_apply, hh, hz, hd] using
    waveRep_remainder z h w hw

theorem hasDerivAt_wave (z : ℝ) : HasDerivAt wave (waveDeriv z) z := by
  apply hasDerivAt_of_quadratic_remainder (C := 1)
  exact Eventually.of_forall fun h => by simpa using wave_remainder z h

theorem continuous_wave : Continuous wave :=
  Differentiable.continuous (𝕜 := ℝ) (fun z => (hasDerivAt_wave z).differentiableAt)

end ThompsonNonamenability.Analytic

end

end OAI

end
end

section
section
namespace OAI

noncomputable section

namespace ThompsonNonamenability.Analytic

open scoped NNReal

def a (t : ℝ) : ℝ :=
  if t ≤ 2 then t / 8 else if t < 3 then 5 / 16 - (3 - t) ^ 2 / 16 else 5 / 16

/-- The derivative profile of `a`, with its common values at the junctions. -/
def aDeriv (t : ℝ) : ℝ :=
  if t ≤ 2 then 1 / 8 else if t < 3 then (3 - t) / 8 else 0

def theta (t : ℝ) : ℝ :=
  if t ≤ 1 then 0 else if t < 2 then (t - 1) ^ 2 / 2 else t - 3 / 2

/-- The derivative profile of `theta`. -/
def thetaDeriv (t : ℝ) : ℝ :=
  if t ≤ 1 then 0 else if t < 2 then t - 1 else 1

/-- The radial coefficient of the modified curve. -/
def b (t : ℝ) : ℝ := min (a t) (-(1 / 8))

/-- The bounded radial correction used in the tube. -/
def q (t : ℝ) : ℝ := -max (a t + 1 / 8) 0

theorem a_of_le_two {t : ℝ} (h : t ≤ 2) : a t = t / 8 := by simp [a, h]

theorem a_of_two_lt_of_lt_three {t : ℝ} (h : 2 < t) (h' : t < 3) :
    a t = 5 / 16 - (3 - t) ^ 2 / 16 := by simp [a, not_le.mpr h, h']

theorem a_of_three_le {t : ℝ} (h : 3 ≤ t) : a t = 5 / 16 := by
  simp [a, show ¬t ≤ 2 by linarith, not_lt.mpr h]

theorem aDeriv_of_le_two {t : ℝ} (h : t ≤ 2) : aDeriv t = 1 / 8 := by
  simp [aDeriv, h]

theorem theta_of_le_one {t : ℝ} (h : t ≤ 1) : theta t = 0 := by simp [theta, h]

theorem theta_of_one_lt_of_lt_two {t : ℝ} (h : 1 < t) (h' : t < 2) :
    theta t = (t - 1) ^ 2 / 2 := by simp [theta, not_le.mpr h, h']

theorem theta_of_two_le {t : ℝ} (h : 2 ≤ t) : theta t = t - 3 / 2 := by
  simp [theta, show ¬t ≤ 1 by linarith, not_lt.mpr h]

theorem thetaDeriv_of_le_one {t : ℝ} (h : t ≤ 1) : thetaDeriv t = 0 := by
  simp [thetaDeriv, h]

theorem thetaDeriv_of_two_le {t : ℝ} (h : 2 ≤ t) : thetaDeriv t = 1 := by
  simp [thetaDeriv, show ¬t ≤ 1 by linarith, not_lt.mpr h]

theorem a_le_five_sixteenths (t : ℝ) : a t ≤ 5 / 16 := by
  unfold a
  split_ifs <;> nlinarith [sq_nonneg (3 - t)]

theorem a_lower_of_one_le {t : ℝ} (h : 1 ≤ t) : 1 / 8 ≤ a t := by
  unfold a
  split_ifs with h₂ h₃
  · linarith
  · have hp : 0 ≤ (t - 2) * (4 - t) := mul_nonneg (by linarith) (by linarith)
    nlinarith
  · norm_num

theorem a_lower_of_two_le {t : ℝ} (h : 2 ≤ t) : 1 / 4 ≤ a t := by
  unfold a
  split_ifs with h₂ h₃
  · linarith
  · have hp : 0 ≤ (t - 2) * (4 - t) := mul_nonneg (by linarith) (by linarith)
    nlinarith
  · norm_num

theorem aDeriv_nonneg (t : ℝ) : 0 ≤ aDeriv t := by
  unfold aDeriv
  split_ifs <;> linarith

theorem aDeriv_le (t : ℝ) : aDeriv t ≤ 1 / 8 := by
  unfold aDeriv
  split_ifs <;> linarith

theorem thetaDeriv_nonneg (t : ℝ) : 0 ≤ thetaDeriv t := by
  unfold thetaDeriv
  split_ifs <;> linarith

theorem thetaDeriv_le (t : ℝ) : thetaDeriv t ≤ 1 := by
  unfold thetaDeriv
  split_ifs <;> linarith

/-- The ordered difference estimate also records monotonicity. -/
theorem a_sub_bounds {x y : ℝ} (hxy : x ≤ y) :
    0 ≤ a y - a x ∧ a y - a x ≤ (y - x) / 8 := by
  by_cases hx₂ : x ≤ 2
  · by_cases hy₂ : y ≤ 2
    · rw [a_of_le_two hx₂, a_of_le_two hy₂]
      constructor <;> linarith
    · by_cases hy₃ : y < 3
      · rw [a_of_le_two hx₂, a_of_two_lt_of_lt_three (lt_of_not_ge hy₂) hy₃]
        have hp : 0 ≤ (y - 2) * (4 - y) := mul_nonneg (by linarith) (by linarith)
        constructor <;> nlinarith [sq_nonneg (y - 2)]
      · rw [a_of_le_two hx₂, a_of_three_le (le_of_not_gt hy₃)]
        constructor <;> linarith
  · by_cases hx₃ : x < 3
    · by_cases hy₃ : y < 3
      · rw [a_of_two_lt_of_lt_three (lt_of_not_ge hx₂) hx₃,
            a_of_two_lt_of_lt_three (by linarith) hy₃]
        have hp : 0 ≤ (y - x) * (6 - x - y) :=
          mul_nonneg (sub_nonneg.mpr hxy) (by linarith)
        have hq : 0 ≤ (y - x) * (x + y - 4) :=
          mul_nonneg (sub_nonneg.mpr hxy) (by linarith)
        constructor <;> nlinarith
      · rw [a_of_two_lt_of_lt_three (lt_of_not_ge hx₂) hx₃,
            a_of_three_le (le_of_not_gt hy₃)]
        have hp : 0 ≤ (3 - x) * (x - 1) := mul_nonneg (by linarith) (by linarith)
        constructor <;> nlinarith [sq_nonneg (3 - x)]
    · rw [a_of_three_le (le_of_not_gt hx₃), a_of_three_le (by linarith)]
      constructor <;> linarith

theorem a_monotone : Monotone a := by
  intro x y hxy
  have := (a_sub_bounds hxy).1
  linarith

/-- Ordered differences of the angular profile. -/
theorem theta_sub_bounds {x y : ℝ} (hxy : x ≤ y) :
    0 ≤ theta y - theta x ∧ theta y - theta x ≤ y - x := by
  by_cases hx₁ : x ≤ 1
  · by_cases hy₁ : y ≤ 1
    · rw [theta_of_le_one hx₁, theta_of_le_one hy₁]
      constructor <;> linarith
    · by_cases hy₂ : y < 2
      · rw [theta_of_le_one hx₁, theta_of_one_lt_of_lt_two (lt_of_not_ge hy₁) hy₂]
        have hp : 0 ≤ (y - 1) * (3 - y) := mul_nonneg (by linarith) (by linarith)
        constructor <;> nlinarith [sq_nonneg (y - 1)]
      · rw [theta_of_le_one hx₁, theta_of_two_le (le_of_not_gt hy₂)]
        constructor <;> linarith
  · by_cases hx₂ : x < 2
    · by_cases hy₂ : y < 2
      · rw [theta_of_one_lt_of_lt_two (lt_of_not_ge hx₁) hx₂,
            theta_of_one_lt_of_lt_two (by linarith) hy₂]
        have hp : 0 ≤ (y - x) * (x + y - 2) :=
          mul_nonneg (sub_nonneg.mpr hxy) (by linarith)
        have hq : 0 ≤ (y - x) * (4 - x - y) :=
          mul_nonneg (sub_nonneg.mpr hxy) (by linarith)
        constructor <;> nlinarith
      · rw [theta_of_one_lt_of_lt_two (lt_of_not_ge hx₁) hx₂,
            theta_of_two_le (le_of_not_gt hy₂)]
        have hp : 0 ≤ (2 - x) * x := mul_nonneg (by linarith) (by linarith)
        constructor <;> nlinarith [sq_nonneg (x - 2)]
    · rw [theta_of_two_le (le_of_not_gt hx₂), theta_of_two_le (by linarith)]
      constructor <;> linarith

theorem theta_monotone : Monotone theta := by
  intro x y hxy
  have := (theta_sub_bounds hxy).1
  linarith

theorem theta_strictMonoOn : StrictMonoOn theta (Set.Ici 1) := by
  intro x hx y hy hxy
  by_cases hx₁ : x ≤ 1
  · have hx : x = 1 := le_antisymm hx₁ hx
    subst x
    rw [theta_of_le_one (le_refl 1)]
    by_cases hy₂ : y < 2
    · rw [theta_of_one_lt_of_lt_two hxy hy₂]
      nlinarith [sq_pos_of_pos (show 0 < y - 1 by linarith)]
    · rw [theta_of_two_le (le_of_not_gt hy₂)]
      linarith
  · by_cases hx₂ : x < 2
    · by_cases hy₂ : y < 2
      · rw [theta_of_one_lt_of_lt_two (lt_of_not_ge hx₁) hx₂,
            theta_of_one_lt_of_lt_two (by linarith) hy₂]
        have hp : 0 < (y - x) * (x + y - 2) := mul_pos (by linarith) (by linarith)
        nlinarith
      · rw [theta_of_one_lt_of_lt_two (lt_of_not_ge hx₁) hx₂,
            theta_of_two_le (le_of_not_gt hy₂)]
        have hp : 0 < (2 - x) * x := mul_pos (by linarith) (by linarith)
        nlinarith
    · rw [theta_of_two_le (le_of_not_gt hx₂), theta_of_two_le (by linarith)]
      linarith

private theorem lipschitz_of_ordered_sub {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : Monotone f) (h : ∀ x y, x ≤ y → f y - f x ≤ (K : ℝ) * (y - x)) :
    LipschitzWith K f := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rcases le_total x y with hxy | hyx
  · simpa only [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr (hf hxy)),
      abs_of_nonpos (sub_nonpos.mpr hxy), neg_sub] using h x y hxy
  · simpa only [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr (hf hyx)),
      abs_of_nonneg (sub_nonneg.mpr hyx)] using h y x hyx

theorem a_lipschitz : LipschitzWith (1 / 8 : ℝ≥0) a := by
  apply lipschitz_of_ordered_sub a_monotone
  intro x y hxy
  norm_num only [NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat]
  linarith [(a_sub_bounds hxy).2]

theorem theta_lipschitz : LipschitzWith 1 theta := by
  apply lipschitz_of_ordered_sub theta_monotone
  intro x y hxy
  simpa using (theta_sub_bounds hxy).2

theorem aDeriv_eq_clip (t : ℝ) : aDeriv t = min (max (3 - t) 0) 1 / 8 := by
  unfold aDeriv
  split_ifs with h₂ h₃
  · rw [max_eq_left (by linarith), min_eq_right (by linarith)]
  · rw [max_eq_left (by linarith), min_eq_left (by linarith)]
  · rw [max_eq_right (by linarith)]
    norm_num

theorem thetaDeriv_eq_clip (t : ℝ) : thetaDeriv t = min (max (t - 1) 0) 1 := by
  unfold thetaDeriv
  split_ifs with h₁ h₂
  · rw [max_eq_right (by linarith)]
    norm_num
  · rw [max_eq_left (by linarith), min_eq_left (by linarith)]
  · rw [max_eq_left (by linarith), min_eq_right (by linarith)]

theorem aDeriv_lipschitz : LipschitzWith (1 / 8 : ℝ≥0) aDeriv := by
  have hbase : LipschitzWith 1 (fun t : ℝ => 3 - t) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simp only [Real.dist_eq, NNReal.coe_one, one_mul]
    have he : (3 - x) - (3 - y) = -(x - y) := by ring
    rw [he, abs_neg]
  have hclip := (hbase.max_const 0).min_const 1
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [Real.dist_eq]
  rw [aDeriv_eq_clip, aDeriv_eq_clip, ← sub_div, abs_div]
  have hc := hclip.dist_le_mul x y
  simp only [Real.dist_eq, NNReal.coe_one, one_mul] at hc
  norm_num only [NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 8)]
  linarith

theorem thetaDeriv_lipschitz : LipschitzWith 1 thetaDeriv := by
  have hbase : LipschitzWith 1 (fun t : ℝ => t - 1) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simp [Real.dist_eq, sub_sub_sub_cancel_right]
  have he : thetaDeriv = fun t => min (max (t - 1) 0) 1 := funext thetaDeriv_eq_clip
  rw [he]
  exact (hbase.max_const 0).min_const 1

theorem q_eq_b_sub_a (t : ℝ) : q t = b t - a t := by
  unfold q b
  by_cases h : a t ≤ -(1 / 8)
  · rw [min_eq_left h, max_eq_right (by linarith)]
    ring
  · rw [min_eq_right (le_of_not_ge h), max_eq_left (by linarith)]
    ring

theorem q_abs_le (t : ℝ) : |q t| ≤ 7 / 16 := by
  rw [q, abs_neg, abs_of_nonneg (le_max_right _ _)]
  apply max_le
  · have := a_le_five_sixteenths t
    linarith
  · norm_num

theorem q_lipschitz : LipschitzWith (1 / 8 : ℝ≥0) q := by
  have hadd : LipschitzWith (1 / 8 : ℝ≥0) (fun t : ℝ => a t + 1 / 8) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [Real.dist_eq, add_sub_add_right_eq_sub] using a_lipschitz.dist_le_mul x y
  have hmax := hadd.max_const 0
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [q, Real.dist_eq, neg_sub_neg, abs_sub_comm] using hmax.dist_le_mul x y

end ThompsonNonamenability.Analytic

end

end OAI

end
end

section
section
namespace OAI

/-!
# Derivatives of the scalar displacement profiles

The one-sided derivatives are glued on the two closed/open half-lines.
In particular, the formulas below hold at all four transition points;
no transition point is removed from the domain.
-/

noncomputable section

open Set Filter
open scoped Topology

namespace ThompsonNonamenability.Analytic

private theorem hasDerivAt_if_le_junction
    {f g : ℝ → ℝ} {c d : ℝ}
    (hf : HasDerivAt f d c) (hg : HasDerivAt g d c)
    (hfg : f c = g c) :
    HasDerivAt (fun t => if t ≤ c then f t else g t) d c := by
  have hleft : HasDerivWithinAt
      (fun t => if t ≤ c then f t else g t) d (Iic c) c := by
    apply hf.hasDerivWithinAt.congr
    · intro t ht
      exact if_pos ht
    · simp
  have hright : HasDerivWithinAt
      (fun t => if t ≤ c then f t else g t) d (Ioi c) c := by
    apply hg.hasDerivWithinAt.congr
    · intro t ht
      exact if_neg (not_le.mpr ht)
    · simpa using hfg
  simpa only [Iic_union_Ioi, hasDerivWithinAt_univ] using hleft.union hright

private theorem hasDerivAt_if_le_all
    {f g df dg : ℝ → ℝ} (c : ℝ)
    (hf : ∀ t, HasDerivAt f (df t) t)
    (hg : ∀ t, HasDerivAt g (dg t) t)
    (hfg : f c = g c) (hdfg : df c = dg c) (t : ℝ) :
    HasDerivAt (fun u => if u ≤ c then f u else g u)
      (if t ≤ c then df t else dg t) t := by
  rcases lt_trichotomy t c with ht | heq | ht
  · rw [if_pos ht.le]
    apply (hf t).congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds ht] with u hu
    exact if_pos hu.le
  · subst t
    rw [if_pos le_rfl]
    exact hasDerivAt_if_le_junction (hf c) ((hg c).congr_deriv hdfg.symm) hfg
  · rw [if_neg (not_le.mpr ht)]
    apply (hg t).congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds ht] with u hu
    exact if_neg (not_le.mpr hu)

private theorem if_lt_eq_if_le
    {f g : ℝ → ℝ} {c : ℝ} (hfg : f c = g c) (t : ℝ) :
    (if t < c then f t else g t) = (if t ≤ c then f t else g t) := by
  rcases lt_trichotomy t c with ht | rfl | ht
  · simp [ht, ht.le]
  · simp [hfg]
  · simp [not_lt.mpr ht.le, not_le.mpr ht]

private theorem hasDerivAt_a_middle (t : ℝ) :
    HasDerivAt (fun u : ℝ => 5 / 16 - (3 - u) ^ 2 / 16) ((3 - t) / 8) t := by
  have h := ((((hasDerivAt_id' t).const_sub 3).fun_pow 2).div_const 16).const_sub
    (5 / 16 : ℝ)
  exact h.congr_deriv (by norm_num ; ring)

private theorem hasDerivAt_theta_middle (t : ℝ) :
    HasDerivAt (fun u : ℝ => (u - 1) ^ 2 / 2) (t - 1) t := by
  have h := (((hasDerivAt_id' t).sub_const 1).fun_pow 2).div_const 2
  exact h.congr_deriv (by norm_num)

/-- The radial scalar profile is differentiable at every real point,
including its two junctions. -/
theorem hasDerivAt_a (t : ℝ) : HasDerivAt a (aDeriv t) t := by
  have hm : ∀ u : ℝ, HasDerivAt
      (fun v : ℝ => if v ≤ 3 then 5 / 16 - (3 - v) ^ 2 / 16 else 5 / 16)
      (if u ≤ 3 then (3 - u) / 8 else 0) u :=
    hasDerivAt_if_le_all 3 hasDerivAt_a_middle
      (fun u => hasDerivAt_const u (5 / 16 : ℝ)) (by norm_num) (by norm_num)
  have h : HasDerivAt
      (fun u : ℝ => if u ≤ 2 then u / 8 else
        if u ≤ 3 then 5 / 16 - (3 - u) ^ 2 / 16 else 5 / 16)
      (if t ≤ 2 then 1 / 8 else if t ≤ 3 then (3 - t) / 8 else 0) t :=
    hasDerivAt_if_le_all 2 (fun u => (hasDerivAt_id u).div_const 8)
      hm (by norm_num) (by norm_num) t
  have hf : a = (fun u : ℝ => if u ≤ 2 then u / 8 else
      if u ≤ 3 then 5 / 16 - (3 - u) ^ 2 / 16 else 5 / 16) := by
    funext u
    by_cases hu : u ≤ 2
    · simp [a, hu]
    · simp only [a, if_neg hu]
      exact if_lt_eq_if_le (f := fun v : ℝ => 5 / 16 - (3 - v) ^ 2 / 16)
        (g := fun _ : ℝ => 5 / 16) (c := 3) (by norm_num) u
  have hd : aDeriv t =
      (if t ≤ 2 then 1 / 8 else if t ≤ 3 then (3 - t) / 8 else 0) := by
    by_cases ht : t ≤ 2
    · simp [aDeriv, ht]
    · simp only [aDeriv, if_neg ht]
      exact if_lt_eq_if_le (f := fun v : ℝ => (3 - v) / 8)
        (g := fun _ : ℝ => 0) (c := 3) (by norm_num) t
  rw [hf, hd]
  exact h

/-- The angular scalar profile is differentiable at every real point,
including its two junctions. -/
theorem hasDerivAt_theta (t : ℝ) : HasDerivAt theta (thetaDeriv t) t := by
  have hm : ∀ u : ℝ, HasDerivAt
      (fun v : ℝ => if v ≤ 2 then (v - 1) ^ 2 / 2 else v - 3 / 2)
      (if u ≤ 2 then u - 1 else 1) u :=
    hasDerivAt_if_le_all 2 hasDerivAt_theta_middle
      (fun u => (hasDerivAt_id u).sub_const (3 / 2 : ℝ))
      (by norm_num) (by norm_num)
  have h : HasDerivAt
      (fun u : ℝ => if u ≤ 1 then 0 else
        if u ≤ 2 then (u - 1) ^ 2 / 2 else u - 3 / 2)
      (if t ≤ 1 then 0 else if t ≤ 2 then t - 1 else 1) t :=
    hasDerivAt_if_le_all 1 (fun u => hasDerivAt_const u (0 : ℝ))
      hm (by norm_num) (by norm_num) t
  have hf : theta = (fun u : ℝ => if u ≤ 1 then 0 else
      if u ≤ 2 then (u - 1) ^ 2 / 2 else u - 3 / 2) := by
    funext u
    by_cases hu : u ≤ 1
    · simp [theta, hu]
    · simp only [theta, if_neg hu]
      exact if_lt_eq_if_le (f := fun v : ℝ => (v - 1) ^ 2 / 2)
        (g := fun v : ℝ => v - 3 / 2) (c := 2) (by norm_num) u
  have hd : thetaDeriv t =
      (if t ≤ 1 then 0 else if t ≤ 2 then t - 1 else 1) := by
    by_cases ht : t ≤ 1
    · simp [thetaDeriv, ht]
    · simp only [thetaDeriv, if_neg ht]
      exact if_lt_eq_if_le (f := fun v : ℝ => v - 1)
        (g := fun _ : ℝ => 1) (c := 2) (by norm_num) t
  rw [hf, hd]
  exact h

theorem differentiable_a : Differentiable ℝ a := fun t => (hasDerivAt_a t).differentiableAt

theorem differentiable_theta : Differentiable ℝ theta :=
  fun t => (hasDerivAt_theta t).differentiableAt

theorem continuous_a : Continuous a := differentiable_a.continuous

theorem continuous_theta : Continuous theta := differentiable_theta.continuous

end ThompsonNonamenability.Analytic

end

end OAI

end
end

section
section
namespace OAI

/-!
# The actual radial oscillating curve

All vectors live in the concrete Euclidean-fiber L² space. The derivative
and squared-speed identities are derived from the scalar profiles and the
frequency curve, including the profile junctions.
-/

noncomputable section

namespace ThompsonNonamenability.Analytic

open Set
open scoped InnerProductSpace

def v (t : ℝ) : Hilbert := wave (theta t)

def gamma (t : ℝ) : Hilbert := a t • v t

def gammaDeriv (t : ℝ) : Hilbert :=
  aDeriv t • v t + (a t * thetaDeriv t) • waveDeriv (theta t)

def u (t : ℝ) : Hilbert := ‖gammaDeriv t‖⁻¹ • gammaDeriv t

theorem v_norm (t : ℝ) : ‖v t‖ = 1 := wave_norm _

theorem continuous_v : Continuous v := continuous_wave.comp continuous_theta

theorem continuous_gamma : Continuous gamma := continuous_a.smul continuous_v

theorem hasDerivAt_v (t : ℝ) :
    HasDerivAt v (thetaDeriv t • waveDeriv (theta t)) t := by
  exact (hasDerivAt_wave (theta t)).scomp t (hasDerivAt_theta t)

theorem hasDerivAt_gamma (t : ℝ) : HasDerivAt gamma (gammaDeriv t) t := by
  have h := (hasDerivAt_a t).fun_smul (hasDerivAt_v t)
  exact h.congr_deriv (by simp only [gammaDeriv, mul_smul, add_comm])

theorem gamma_norm (t : ℝ) : ‖gamma t‖ = |a t| := by
  simp only [gamma, norm_smul, Real.norm_eq_abs, v_norm, mul_one]

@[simp] theorem gamma_zero : gamma 0 = 0 := by
  simp [gamma, a_of_le_two (by norm_num : (0 : ℝ) ≤ 2)]

theorem gamma_of_le_one {t : ℝ} (ht : t ≤ 1) : gamma t = (t / 8) • wave 0 := by
  rw [gamma, a_of_le_two (by linarith), v, theta_of_le_one ht]

theorem gammaDeriv_of_le_one {t : ℝ} (ht : t ≤ 1) :
    gammaDeriv t = (1 / 8 : ℝ) • wave 0 := by
  simp [gammaDeriv, v, aDeriv_of_le_two (by linarith : t ≤ 2),
    theta_of_le_one ht, thetaDeriv_of_le_one ht]

theorem gammaDeriv_norm_sq (t : ℝ) :
    ‖gammaDeriv t‖ ^ 2 = (aDeriv t) ^ 2 + (a t) ^ 2 * (thetaDeriv t) ^ 2 / 3 := by
  rw [gammaDeriv, norm_add_sq_real]
  simp only [norm_smul, Real.norm_eq_abs, mul_one, mul_pow, sq_abs,
    waveDeriv_norm_sq, real_inner_smul_left, real_inner_smul_right,
    v, wave_norm, wave_inner_waveDeriv, mul_zero, add_zero]
  ring

theorem gammaDeriv_speed_lower (t : ℝ) : (1 / 8 : ℝ) ≤ ‖gammaDeriv t‖ := by
  have heq := gammaDeriv_norm_sq t
  have hn := norm_nonneg (gammaDeriv t)
  by_cases ht : t ≤ 2
  · rw [aDeriv_of_le_two ht] at heq
    nlinarith [mul_nonneg (sq_nonneg (a t)) (sq_nonneg (thetaDeriv t))]
  · have ha := a_lower_of_two_le (le_of_not_ge ht)
    rw [thetaDeriv_of_two_le (le_of_not_ge ht)] at heq
    nlinarith [sq_nonneg (aDeriv t), sq_nonneg (a t - 1 / 4)]

theorem gammaDeriv_norm_pos (t : ℝ) : 0 < ‖gammaDeriv t‖ := by
  have := gammaDeriv_speed_lower t
  linarith

theorem gammaDeriv_ne_zero (t : ℝ) : gammaDeriv t ≠ 0 :=
  norm_pos_iff.mp (gammaDeriv_norm_pos t)

theorem u_norm (t : ℝ) : ‖u t‖ = 1 :=
  norm_smul_inv_norm (gammaDeriv_ne_zero t)

theorem gammaDeriv_eq_norm_smul_u (t : ℝ) :
    gammaDeriv t = ‖gammaDeriv t‖ • u t := by
  simp only [u, smul_smul, mul_inv_cancel₀ (ne_of_gt (gammaDeriv_norm_pos t)), one_smul]

theorem u_of_le_one {t : ℝ} (ht : t ≤ 1) : u t = v t := by
  rw [u, gammaDeriv_of_le_one ht]
  simp [v, theta_of_le_one ht, norm_smul, wave_norm, smul_smul]

theorem gammaDeriv_inner_v (t : ℝ) : inner (𝕜 := ℝ) (gammaDeriv t) (v t) = aDeriv t := by
  have hz : inner (𝕜 := ℝ) (waveDeriv (theta t)) (v t) = 0 := by
    rw [real_inner_comm]
    exact wave_inner_waveDeriv _
  simp [gammaDeriv, inner_add_left, real_inner_smul_left, hz, v_norm]

theorem u_inner_v (t : ℝ) : inner (𝕜 := ℝ) (u t) (v t) = aDeriv t / ‖gammaDeriv t‖ := by
  simp only [u, real_inner_smul_left, gammaDeriv_inner_v, div_eq_mul_inv]
  ring

theorem u_inner_v_nonneg (t : ℝ) : 0 ≤ inner (𝕜 := ℝ) (u t) (v t) := by
  rw [u_inner_v]
  exact div_nonneg (aDeriv_nonneg t) (norm_nonneg _)

theorem v_inner (s t : ℝ) : inner (𝕜 := ℝ) (v s) (v t) = sinc (theta t - theta s) :=
  wave_inner _ _

theorem gamma_inner (s t : ℝ) :
    inner (𝕜 := ℝ) (gamma s) (gamma t) = a s * a t * sinc (theta t - theta s) := by
  simp only [gamma, real_inner_smul_left, real_inner_smul_right, v_inner]
  ring

theorem gamma_sub_norm_sq (s t : ℝ) :
    ‖gamma t - gamma s‖ ^ 2 = (a s) ^ 2 + (a t) ^ 2 -
      2 * (a s * a t * sinc (theta t - theta s)) := by
  rw [norm_sub_rev, norm_sub_sq_real, gamma_norm, gamma_norm, sq_abs, sq_abs,
    gamma_inner]
  ring

theorem gammaDeriv_speed_eq_of_le_one {t : ℝ} (ht : t ≤ 1) :
    ‖gammaDeriv t‖ = 1 / 8 := by
  rw [gammaDeriv_of_le_one ht, norm_smul, Real.norm_eq_abs, wave_norm]
  norm_num

end ThompsonNonamenability.Analytic

end

end OAI

end
end

section
section
namespace OAI

noncomputable section


namespace ThompsonNonamenability.Analytic

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Negative radial normalization, with the field's usual value at zero. -/
def normalizeNeg (z : E) : E := -(‖z‖⁻¹ • z)

theorem norm_normalizeNeg {z : E} (hz : z ≠ 0) : ‖normalizeNeg z‖ = 1 := by
  have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  rw [normalizeNeg, norm_neg, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (norm_nonneg z)), inv_mul_cancel₀ hn]

/-- A scalar identity used to avoid any estimate depending on the larger norm. -/
private theorem abs_inv_sub_mul {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    |a⁻¹ - b⁻¹| * b = |b - a| / a := by
  have hdiff : a⁻¹ - b⁻¹ = (b - a) / (a * b) := by
    field_simp [ha.ne', hb.ne']
  rw [hdiff, abs_div, abs_mul, abs_of_pos ha, abs_of_pos hb]
  field_simp [ha.ne', hb.ne']

/-- Radial normalization is `2 / ε`-Lipschitz where the norm is at least `ε`. -/
theorem normalizeNeg_lipschitz {ε : ℝ} (hε : 0 < ε) {x y : E}
    (hx : ε ≤ ‖x‖) (hy : ε ≤ ‖y‖) :
    ‖normalizeNeg x - normalizeNeg y‖ ≤ (2 / ε) * ‖x - y‖ := by
  have hxp : 0 < ‖x‖ := hε.trans_le hx
  have hyp : 0 < ‖y‖ := hε.trans_le hy
  have hdecomp : ‖x‖⁻¹ • x - ‖y‖⁻¹ • y =
      ‖x‖⁻¹ • (x - y) + (‖x‖⁻¹ - ‖y‖⁻¹) • y := by
    simp only [smul_sub, sub_smul]
    abel
  have hneg : normalizeNeg x - normalizeNeg y =
      -(‖x‖⁻¹ • x - ‖y‖⁻¹ • y) := by
    simp only [normalizeNeg, neg_sub]
    abel
  calc
    ‖normalizeNeg x - normalizeNeg y‖ =
        ‖‖x‖⁻¹ • x - ‖y‖⁻¹ • y‖ := by rw [hneg, norm_neg]
    _ ≤ ‖‖x‖⁻¹ • (x - y)‖ + ‖(‖x‖⁻¹ - ‖y‖⁻¹) • y‖ := by
      rw [hdecomp]
      exact norm_add_le _ _
    _ = ‖x‖⁻¹ * ‖x - y‖ + |‖y‖ - ‖x‖| / ‖x‖ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hxp), abs_inv_sub_mul hxp hyp]
    _ ≤ ‖x‖⁻¹ * ‖x - y‖ + ‖x - y‖ / ‖x‖ := by
      apply add_le_add le_rfl
      exact div_le_div_of_nonneg_right
        (by simpa only [norm_sub_rev] using abs_norm_sub_norm_le y x) (norm_nonneg x)
    _ = (2 / ‖x‖) * ‖x - y‖ := by ring
    _ ≤ (2 / ε) * ‖x - y‖ :=
      mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_left (by norm_num) hε hx) (norm_nonneg _)

/-- Normalize the given nonvanishing map and retain the closed-ball carrier. -/
def normalizedMap (G : UnitBall E → E) {ε : ℝ} (hε : 0 < ε)
    (hLower : ∀ x, ε ≤ ‖G x‖) : UnitBall E → UnitBall E :=
  fun x => ⟨normalizeNeg (G x), le_of_eq (norm_normalizeNeg
    (norm_pos_iff.mp (hε.trans_le (hLower x))))⟩

@[simp] theorem coe_normalizedMap (G : UnitBall E → E) {ε : ℝ} (hε : 0 < ε)
    (hLower : ∀ x, ε ≤ ‖G x‖) (x : UnitBall E) :
    (normalizedMap G hε hLower x : E) = normalizeNeg (G x) := rfl

theorem norm_normalizedMap (G : UnitBall E → E) {ε : ℝ} (hε : 0 < ε)
    (hLower : ∀ x, ε ≤ ‖G x‖) (x : UnitBall E) :
    ‖(normalizedMap G hε hLower x : E)‖ = 1 :=
  norm_normalizeNeg (norm_pos_iff.mp (hε.trans_le (hLower x)))

/-- The outer identity and unit normalization give a displacement of at least `1/2`. -/
theorem normalizedMap_displacement (G : UnitBall E → E) {ε : ℝ} (hε : 0 < ε)
    (hLower : ∀ x, ε ≤ ‖G x‖)
    (hOuter : ∀ x : UnitBall E, (1 / 2 : ℝ) ≤ ‖(x : E)‖ → G x = (x : E))
    (x : UnitBall E) :
    (1 / 2 : ℝ) ≤ ‖(normalizedMap G hε hLower x : E) - (x : E)‖ := by
  by_cases hx : (1 / 2 : ℝ) ≤ ‖(x : E)‖
  · have hxp : 0 < ‖(x : E)‖ := by linarith
    have hi : 0 ≤ ‖(x : E)‖⁻¹ + 1 := by
      have := inv_nonneg.mpr (norm_nonneg (x : E))
      linarith
    have heq : normalizeNeg (x : E) - (x : E) =
        -((‖(x : E)‖⁻¹ + 1) • (x : E)) := by
      simp only [normalizeNeg, add_smul, one_smul, neg_add_rev]
      abel
    rw [coe_normalizedMap, hOuter x hx, heq, norm_neg, norm_smul,
      Real.norm_eq_abs, abs_of_nonneg hi, add_mul, one_mul,
      inv_mul_cancel₀ hxp.ne']
    linarith
  · have hrev := norm_sub_norm_le (normalizedMap G hε hLower x : E) (x : E)
    rw [norm_normalizedMap] at hrev
    linarith

/-- The concrete normalized map inherits the advertised Lipschitz estimate. -/
theorem normalizedMap_lipschitz (G : UnitBall E → E) {ε C : ℝ} (hε : 0 < ε)
    (hLower : ∀ x, ε ≤ ‖G x‖)
    (hLip : ∀ x y : UnitBall E, ‖G x - G y‖ ≤ C * ‖(x : E) - (y : E)‖)
    (x y : UnitBall E) :
    ‖(normalizedMap G hε hLower x : E) - (normalizedMap G hε hLower y : E)‖ ≤
      (2 * C / ε) * ‖(x : E) - (y : E)‖ := by
  calc
    _ ≤ (2 / ε) * ‖G x - G y‖ := normalizeNeg_lipschitz hε (hLower x) (hLower y)
    _ ≤ (2 / ε) * (C * ‖(x : E) - (y : E)‖) :=
      mul_le_mul_of_nonneg_left (hLip x y) (div_nonneg (by norm_num) hε.le)
    _ = _ := by ring

end ThompsonNonamenability.Analytic

end

end OAI

end
end

section
section
namespace OAI

/-!
# Quantitative estimates for the actual Hilbert curve

The derivative estimate uses first-derivative product differences on the
oscillating part and the exact straight-tail formula. No second derivative
at a profile junction is assumed.
-/

noncomputable section

namespace ThompsonNonamenability.Analytic

open Set
open scoped NNReal

theorem a_sub_abs_le (s t : ℝ) : |a s - a t| ≤ (1 / 8) * |s - t| := by
  simpa only [Real.dist_eq, NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat] using
    a_lipschitz.dist_le_mul s t

theorem aDeriv_sub_abs_le (s t : ℝ) :
    |aDeriv s - aDeriv t| ≤ (1 / 8) * |s - t| := by
  simpa only [Real.dist_eq, NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat] using
    aDeriv_lipschitz.dist_le_mul s t

theorem theta_sub_abs_le (s t : ℝ) : |theta s - theta t| ≤ |s - t| := by
  simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using theta_lipschitz.dist_le_mul s t

theorem thetaDeriv_sub_abs_le (s t : ℝ) :
    |thetaDeriv s - thetaDeriv t| ≤ |s - t| := by
  simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using
    thetaDeriv_lipschitz.dist_le_mul s t

theorem waveDeriv_norm_le_one (z : ℝ) : ‖waveDeriv z‖ ≤ 1 := by
  have := waveDeriv_norm_sq z
  nlinarith [norm_nonneg (waveDeriv z)]

theorem v_sub_norm_le_forward (s t : ℝ) : ‖v s - v t‖ ≤ |s - t| :=
  (wave_sub_norm_le (theta s) (theta t)).trans (theta_sub_abs_le s t)

theorem v_lipschitz : LipschitzWith 1 v := by
  apply LipschitzWith.of_dist_le_mul
  intro s t
  simpa only [dist_eq_norm, Real.norm_eq_abs, NNReal.coe_one, one_mul] using
    v_sub_norm_le_forward s t

/-- A product difference estimate with the coefficient difference at the first vector. -/
theorem smul_sub_smul_norm_le (r q : ℝ) (x y : Hilbert) :
    ‖r • x - q • y‖ ≤ |r - q| * ‖x‖ + |q| * ‖x - y‖ := by
  have he : r • x - q • y = (r - q) • x + q • (x - y) := by
    simp only [sub_smul, smul_sub]
    abel
  rw [he]
  simpa only [norm_smul, Real.norm_eq_abs] using
    norm_add_le ((r - q) • x) (q • (x - y))

/-- The second coefficient in the derivative is nonnegative and uniformly bounded. -/
theorem angularCoeff_bounds {t : ℝ} (ht : 1 ≤ t) :
    0 ≤ a t * thetaDeriv t ∧ a t * thetaDeriv t ≤ 5 / 16 := by
  have ha : 0 ≤ a t := by have := a_lower_of_one_le ht; linarith
  constructor
  · exact mul_nonneg ha (thetaDeriv_nonneg t)
  · exact (mul_le_of_le_one_right ha (thetaDeriv_le t)).trans (a_le_five_sixteenths t)

theorem angularCoeff_sub_abs_le {s t : ℝ} (_hs : 1 ≤ s) (ht : 1 ≤ t) :
    |a s * thetaDeriv s - a t * thetaDeriv t| ≤ (7 / 16) * |s - t| := by
  have ha : 0 ≤ a t := by have := a_lower_of_one_le ht; linarith
  have he : a s * thetaDeriv s - a t * thetaDeriv t =
      (a s - a t) * thetaDeriv s + a t * (thetaDeriv s - thetaDeriv t) := by ring
  calc
    _ ≤ |a s - a t| * |thetaDeriv s| + |a t| * |thetaDeriv s - thetaDeriv t| := by
      rw [he]
      simpa only [abs_mul] using
        abs_add_le ((a s - a t) * thetaDeriv s) (a t * (thetaDeriv s - thetaDeriv t))
    _ = |a s - a t| * thetaDeriv s + a t * |thetaDeriv s - thetaDeriv t| := by
      rw [abs_of_nonneg (thetaDeriv_nonneg s), abs_of_nonneg ha]
    _ ≤ ((1 / 8) * |s - t|) * 1 + (5 / 16) * |s - t| := by
      apply add_le_add
      · exact mul_le_mul (a_sub_abs_le s t) (thetaDeriv_le s)
          (thetaDeriv_nonneg s) (mul_nonneg (by norm_num) (abs_nonneg _))
      · exact mul_le_mul (a_le_five_sixteenths t) (thetaDeriv_sub_abs_le s t)
          (abs_nonneg _) (by norm_num)
    _ = _ := by ring

/-- A global upper speed bound, including the unbounded negative straight tail. -/
theorem gammaDeriv_speed_upper (t : ℝ) : ‖gammaDeriv t‖ ≤ 7 / 16 := by
  by_cases ht : t ≤ 1
  · rw [gammaDeriv_speed_eq_of_le_one ht]
    norm_num
  · have hb := angularCoeff_bounds (le_of_not_ge ht)
    calc
      ‖gammaDeriv t‖ ≤ ‖aDeriv t • v t‖ +
          ‖(a t * thetaDeriv t) • waveDeriv (theta t)‖ := norm_add_le _ _
      _ = aDeriv t + (a t * thetaDeriv t) * ‖waveDeriv (theta t)‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg (aDeriv_nonneg t), abs_of_nonneg hb.1, v_norm, mul_one]
      _ ≤ 1 / 8 + 5 / 16 := by
        apply add_le_add (aDeriv_le t)
        exact (mul_le_of_le_one_right hb.1 (waveDeriv_norm_le_one _)).trans hb.2
      _ = 7 / 16 := by norm_num

/-- The ordinary mean value estimate applied to the proved derivative. -/
theorem gamma_sub_norm_le_forward (s t : ℝ) : ‖gamma s - gamma t‖ ≤ (7 / 16) * |s - t| := by
  have h : ‖gamma s - gamma t‖ ≤ (7 / 16) * ‖s - t‖ :=
    Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (s := (Set.univ : Set ℝ)) (fun x _ => (hasDerivAt_gamma x).hasDerivWithinAt)
      (fun x _ => gammaDeriv_speed_upper x) convex_univ (mem_univ t) (mem_univ s)
  simpa only [Real.norm_eq_abs] using h

/-- On the oscillating tail, product differences give the derivative estimate. -/
private theorem gammaDeriv_sub_norm_le_tail {s t : ℝ} (hs : 1 ≤ s) (ht : 1 ≤ t) :
    ‖gammaDeriv s - gammaDeriv t‖ ≤ |s - t| := by
  have hrad := smul_sub_smul_norm_le (aDeriv s) (aDeriv t) (v s) (v t)
  rw [v_norm, mul_one, abs_of_nonneg (aDeriv_nonneg t)] at hrad
  have hradMul := mul_le_mul (aDeriv_le t) (v_sub_norm_le_forward s t)
    (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1 / 8)
  have hradBound : ‖aDeriv s • v s - aDeriv t • v t‖ ≤ (1 / 4) * |s - t| := by
    linarith [aDeriv_sub_abs_le s t]
  have hb := angularCoeff_bounds ht
  have hwd := (waveDeriv_sub_norm_le (theta s) (theta t)).trans (theta_sub_abs_le s t)
  have hm₁ : |a s * thetaDeriv s - a t * thetaDeriv t| * ‖waveDeriv (theta s)‖ ≤
      (7 / 16) * |s - t| :=
    (mul_le_of_le_one_right (abs_nonneg _) (waveDeriv_norm_le_one _)).trans
      (angularCoeff_sub_abs_le hs ht)
  have hm₂ := mul_le_mul hb.2 hwd (norm_nonneg _)
    (by norm_num : (0 : ℝ) ≤ 5 / 16)
  have hang := smul_sub_smul_norm_le (a s * thetaDeriv s) (a t * thetaDeriv t)
    (waveDeriv (theta s)) (waveDeriv (theta t))
  rw [abs_of_nonneg hb.1] at hang
  have hangBound : ‖(a s * thetaDeriv s) • waveDeriv (theta s) -
      (a t * thetaDeriv t) • waveDeriv (theta t)‖ ≤ (3 / 4) * |s - t| := by
    linarith
  have he : gammaDeriv s - gammaDeriv t =
      (aDeriv s • v s - aDeriv t • v t) +
      ((a s * thetaDeriv s) • waveDeriv (theta s) -
        (a t * thetaDeriv t) • waveDeriv (theta t)) := by
    dsimp [gammaDeriv]
    abel
  rw [he]
  exact (norm_add_le _ _).trans (by linarith)

/-- The constant derivative on the straight tail joins the oscillating estimate at one. -/
theorem gammaDeriv_sub_norm_le_forward (s t : ℝ) :
    ‖gammaDeriv s - gammaDeriv t‖ ≤ |s - t| := by
  have hord : ∀ s t : ℝ, s ≤ t → ‖gammaDeriv s - gammaDeriv t‖ ≤ |s - t| := by
    intro s t hst
    by_cases ht : t ≤ 1
    · rw [gammaDeriv_of_le_one (hst.trans ht), gammaDeriv_of_le_one ht,
        sub_self, norm_zero]
      exact abs_nonneg _
    · have ht1 : 1 ≤ t := (lt_of_not_ge ht).le
      by_cases hs : 1 ≤ s
      · exact gammaDeriv_sub_norm_le_tail hs ht1
      · have hs1 : s ≤ 1 := (lt_of_not_ge hs).le
        calc
          ‖gammaDeriv s - gammaDeriv t‖ = ‖gammaDeriv 1 - gammaDeriv t‖ := by
            rw [gammaDeriv_of_le_one hs1, gammaDeriv_of_le_one (le_refl 1)]
          _ ≤ |1 - t| := gammaDeriv_sub_norm_le_tail (le_refl 1) ht1
          _ ≤ |s - t| := by
            rw [abs_of_nonpos (sub_nonpos.mpr ht1),
              abs_of_nonpos (sub_nonpos.mpr hst)]
            linarith
  rcases le_total s t with hst | hts
  · exact hord s t hst
  · calc
      ‖gammaDeriv s - gammaDeriv t‖ = ‖gammaDeriv t - gammaDeriv s‖ := norm_sub_rev _ _
      _ ≤ |t - s| := hord t s hts
      _ = |s - t| := abs_sub_comm _ _

/-- Normalize the actual nonzero tangent using its proved speed lower bound. -/
theorem u_sub_norm_le_forward (s t : ℝ) : ‖u s - u t‖ ≤ 16 * |s - t| := by
  have hn := normalizeNeg_lipschitz (by norm_num : (0 : ℝ) < 1 / 8)
    (gammaDeriv_speed_lower s) (gammaDeriv_speed_lower t)
  have he : normalizeNeg (gammaDeriv s) - normalizeNeg (gammaDeriv t) =
      -(u s - u t) := by simp only [normalizeNeg, u, neg_sub, neg_sub_neg]
  rw [he, norm_neg, show (2 / (1 / 8 : ℝ)) = 16 by norm_num] at hn
  exact hn.trans (mul_le_mul_of_nonneg_left (gammaDeriv_sub_norm_le_forward s t)
    (by norm_num))

theorem u_lipschitz : LipschitzWith 16 u := by
  apply LipschitzWith.of_dist_le_mul
  intro s t
  simpa only [dist_eq_norm, Real.norm_eq_abs, NNReal.coe_ofNat] using
    u_sub_norm_le_forward s t

/-- Pairwise estimates with the base parameter first. -/
theorem v_sub_norm_le (s t : ℝ) : ‖v t - v s‖ ≤ |t - s| :=
  v_sub_norm_le_forward t s

theorem gamma_sub_norm_le (s t : ℝ) : ‖gamma t - gamma s‖ ≤ (7 / 16) * |t - s| :=
  gamma_sub_norm_le_forward t s

theorem gammaDeriv_sub_norm_le (s t : ℝ) : ‖gammaDeriv t - gammaDeriv s‖ ≤ |t - s| :=
  gammaDeriv_sub_norm_le_forward t s

theorem u_sub_norm_le (s t : ℝ) : ‖u t - u s‖ ≤ 16 * |t - s| :=
  u_sub_norm_le_forward t s

theorem lipschitzWith_v : LipschitzWith 1 v := v_lipschitz

theorem lipschitzWith_u : LipschitzWith 16 u := u_lipschitz

end ThompsonNonamenability.Analytic

end

end OAI

end
end

section
section
namespace OAI

/-!
# The rank-two rotations in the displacement construction

These are actual bounded operators on a real inner-product space. The formula
has no choice of orthogonal complement and remains valid when the two unit
vectors coincide. The estimates use the operator norm.
-/

noncomputable section


namespace ThompsonNonamenability.Analytic

open scoped InnerProductSpace NNReal

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The skew rank-two operator associated with an ordered pair. -/
def skew (u v : E) : E →L[ℝ] E :=
  (innerSL ℝ u).smulRight v - (innerSL ℝ v).smulRight u

@[simp] theorem skew_apply (u v x : E) :
    skew u v x = ⟪u, x⟫_ℝ • v - ⟪v, x⟫_ℝ • u := rfl

/-- The rotation taking `u` to `v`, on the non-antipodal unit-pair domain. -/
def rotation (u v : E) : E →L[ℝ] E :=
  ContinuousLinearMap.id ℝ E + skew u v +
    (1 + ⟪u, v⟫_ℝ)⁻¹ • (skew u v).comp (skew u v)

theorem rotation_apply (u v x : E) :
    rotation u v x = x + skew u v x +
      (1 + ⟪u, v⟫_ℝ)⁻¹ • skew u v (skew u v x) := rfl

@[simp] theorem skew_self (u : E) : skew u u = 0 := by
  simp [skew]

@[simp] theorem rotation_self (u : E) :
    rotation u u = ContinuousLinearMap.id ℝ E := by
  simp [rotation]

theorem rotation_apply_explicit (u v x : E)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    rotation u v x = x +
      (⟪u, x⟫_ℝ + (1 + ⟪u, v⟫_ℝ)⁻¹ *
        (⟪u, v⟫_ℝ * ⟪u, x⟫_ℝ - ⟪v, x⟫_ℝ)) • v +
      (-⟪v, x⟫_ℝ + (1 + ⟪u, v⟫_ℝ)⁻¹ *
        (⟪u, v⟫_ℝ * ⟪v, x⟫_ℝ - ⟪u, x⟫_ℝ)) • u := by
  have huu : ⟪u, u⟫_ℝ = 1 := by
    rw [real_inner_self_eq_norm_sq, hu]; norm_num
  have hvv : ⟪v, v⟫_ℝ = 1 := by
    rw [real_inner_self_eq_norm_sq, hv]; norm_num
  simp only [rotation_apply, skew_apply, inner_sub_right,
    real_inner_smul_right, huu, hvv, real_inner_comm u v]
  module

theorem rotation_apply_self (u v : E)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hκ : 0 ≤ ⟪u, v⟫_ℝ) :
    rotation u v u = v := by
  have huu : ⟪u, u⟫_ℝ = 1 := by
    rw [real_inner_self_eq_norm_sq, hu]; norm_num
  have hd : 1 + ⟪u, v⟫_ℝ ≠ 0 := by linarith
  rw [rotation_apply_explicit u v u hu hv, huu, real_inner_comm u v]
  match_scalars <;> field_simp [hd] <;> ring

theorem rotation_inner (u v : E)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hκ : 0 ≤ ⟪u, v⟫_ℝ)
    (x y : E) :
    ⟪rotation u v x, rotation u v y⟫_ℝ = ⟪x, y⟫_ℝ := by
  have huu : ⟪u, u⟫_ℝ = 1 := by
    rw [real_inner_self_eq_norm_sq, hu]; norm_num
  have hvv : ⟪v, v⟫_ℝ = 1 := by
    rw [real_inner_self_eq_norm_sq, hv]; norm_num
  have hd : 1 + ⟪u, v⟫_ℝ ≠ 0 := by linarith
  rw [rotation_apply_explicit u v x hu hv,
    rotation_apply_explicit u v y hu hv]
  simp only [inner_add_left, inner_add_right, real_inner_smul_left,
    real_inner_smul_right, huu, hvv, real_inner_comm u v,
    real_inner_comm u x, real_inner_comm v x]
  field_simp [hd]
  ring

theorem rotation_norm (u v : E)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hκ : 0 ≤ ⟪u, v⟫_ℝ)
    (x : E) : ‖rotation u v x‖ = ‖x‖ := by
  rw [norm_eq_sqrt_real_inner, rotation_inner u v hu hv hκ,
    ← norm_eq_sqrt_real_inner]

def rankOne (u v : E) : E →L[ℝ] E := (innerSL ℝ u).smulRight v

/-- The operator polynomial used in the rank-two rotation formula. -/
def rotationPolynomial (A : E →L[ℝ] E) (c : ℝ) : E →L[ℝ] E :=
  ContinuousLinearMap.id ℝ E + A + c • A.comp A

@[simp] lemma norm_rankOne (u v : E) : ‖rankOne u v‖ = ‖u‖ * ‖v‖ := by
  simp only [rankOne, ContinuousLinearMap.norm_smulRight_apply, innerSL_apply_norm]

lemma rankOne_sub (u v u' v' : E) :
    rankOne u v - rankOne u' v' =
      rankOne (u - u') v + rankOne u' (v - v') := by
  ext x
  simp only [rankOne, sub_apply, add_apply,
    ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, inner_sub_left,
    sub_smul, smul_sub]
  abel

lemma norm_rankOne_sub_le (u v u' v' : E) :
    ‖rankOne u v - rankOne u' v'‖ ≤
      ‖u - u'‖ * ‖v‖ + ‖u'‖ * ‖v - v'‖ := by
  rw [rankOne_sub]
  simpa only [norm_rankOne] using
    norm_add_le (rankOne (u - u') v) (rankOne u' (v - v'))

lemma norm_skew_le_two (u v : E) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    ‖skew u v‖ ≤ 2 := by
  calc
    ‖skew u v‖ ≤ ‖rankOne u v‖ + ‖rankOne v u‖ := norm_sub_le _ _
    _ = 2 := by simp only [norm_rankOne, hu, hv]; norm_num

lemma norm_skew_sub_le (u v u' v' : E)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hu' : ‖u'‖ = 1) (hv' : ‖v'‖ = 1) :
    ‖skew u v - skew u' v'‖ ≤ 2 * (‖u - u'‖ + ‖v - v'‖) := by
  have heq : skew u v - skew u' v' =
      (rankOne u v - rankOne u' v') - (rankOne v u - rankOne v' u') := by
    unfold skew rankOne
    abel
  have h₁ := norm_rankOne_sub_le u v u' v'
  have h₂ := norm_rankOne_sub_le v u v' u'
  rw [hv, hu', mul_one, one_mul] at h₁
  rw [hu, hv', mul_one, one_mul] at h₂
  rw [heq]
  calc
    _ ≤ ‖rankOne u v - rankOne u' v'‖ + ‖rankOne v u - rankOne v' u'‖ :=
      norm_sub_le _ _
    _ ≤ (‖u - u'‖ + ‖v - v'‖) + (‖v - v'‖ + ‖u - u'‖) :=
      add_le_add h₁ h₂
    _ = 2 * (‖u - u'‖ + ‖v - v'‖) := by ring

lemma inner_sub_inner_le (u v u' v' : E) (hv : ‖v‖ = 1) (hu' : ‖u'‖ = 1) :
    |⟪u, v⟫_ℝ - ⟪u', v'⟫_ℝ| ≤ ‖u - u'‖ + ‖v - v'‖ := by
  have heq : ⟪u, v⟫_ℝ - ⟪u', v'⟫_ℝ =
      ⟪u - u', v⟫_ℝ + ⟪u', v - v'⟫_ℝ := by
    rw [inner_sub_left, inner_sub_right]
    ring
  calc
    |⟪u, v⟫_ℝ - ⟪u', v'⟫_ℝ| =
        ‖⟪u - u', v⟫_ℝ + ⟪u', v - v'⟫_ℝ‖ := by
      rw [heq, Real.norm_eq_abs]
    _ ≤ ‖⟪u - u', v⟫_ℝ‖ + ‖⟪u', v - v'⟫_ℝ‖ := norm_add_le _ _
    _ ≤ ‖u - u'‖ * ‖v‖ + ‖u'‖ * ‖v - v'‖ :=
      add_le_add (norm_inner_le_norm _ _) (norm_inner_le_norm _ _)
    _ = ‖u - u'‖ + ‖v - v'‖ := by rw [hv, hu', mul_one, one_mul]

lemma inverse_one_add_bounds (κ : ℝ) (hκ : 0 ≤ κ) :
    0 ≤ (1 + κ)⁻¹ ∧ (1 + κ)⁻¹ ≤ 1 := by
  constructor
  · exact inv_nonneg.mpr (by linarith)
  · exact inv_le_one_of_one_le₀ (by linarith)

lemma inverse_one_add_difference (κ κ' d : ℝ)
    (hκ : 0 ≤ κ) (hκ' : 0 ≤ κ') (h : |κ - κ'| ≤ d) :
    |(1 + κ)⁻¹ - (1 + κ')⁻¹| ≤ d := by
  have hp : 0 < 1 + κ := by linarith
  have hp' : 0 < 1 + κ' := by linarith
  have hsub : (1 + κ') - (1 + κ) = κ' - κ := by ring
  calc
    |(1 + κ)⁻¹ - (1 + κ')⁻¹|
        = |κ - κ'| / ((1 + κ) * (1 + κ')) := by
          rw [inv_sub_inv (ne_of_gt hp) (ne_of_gt hp'), abs_div,
            abs_of_pos (mul_pos hp hp'), hsub, abs_sub_comm κ' κ]
    _ ≤ |κ - κ'| :=
      div_le_self (abs_nonneg _) (by nlinarith [mul_nonneg hκ hκ'])
    _ ≤ d := h

-- This lemma is independent of the rank-two construction.
lemma norm_rotationPolynomial_sub_le (A B : E →L[ℝ] E) (c c' d : ℝ)
    (hd : 0 ≤ d) (hA : ‖A‖ ≤ 2) (hB : ‖B‖ ≤ 2)
    (hAB : ‖A - B‖ ≤ 2 * d) (hcc' : |c - c'| ≤ d)
    (hc' : |c'| ≤ 1) :
    ‖rotationPolynomial A c - rotationPolynomial B c'‖ ≤ 14 * d := by
  have hAA : ‖A.comp A‖ ≤ 4 := by
    calc
      ‖A.comp A‖ ≤ ‖A‖ * ‖A‖ := A.opNorm_comp_le A
      _ ≤ 2 * 2 := mul_le_mul hA hA (norm_nonneg _) (by norm_num)
      _ = 4 := by norm_num
  have h2d : 0 ≤ 2 * d := mul_nonneg (by norm_num) hd
  have hsquare : A.comp A - B.comp B = (A - B).comp A + B.comp (A - B) := by
    rw [ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub]
    abel
  have hsq : ‖A.comp A - B.comp B‖ ≤ 8 * d := by
    rw [hsquare]
    calc
      _ ≤ ‖(A - B).comp A‖ + ‖B.comp (A - B)‖ := norm_add_le _ _
      _ ≤ ‖A - B‖ * ‖A‖ + ‖B‖ * ‖A - B‖ :=
        add_le_add ((A - B).opNorm_comp_le A) (B.opNorm_comp_le (A - B))
      _ ≤ (2 * d) * 2 + 2 * (2 * d) :=
        add_le_add (mul_le_mul hAB hA (norm_nonneg _) h2d)
          (mul_le_mul hB hAB (norm_nonneg _) (by norm_num))
      _ = 8 * d := by ring
  have hcoeff : ‖(c - c') • A.comp A‖ ≤ 4 * d := by
    calc
      ‖(c - c') • A.comp A‖ ≤ |c - c'| * ‖A.comp A‖ := by
        simpa only [Real.norm_eq_abs] using
          ContinuousLinearMap.opNorm_smul_le (c - c') (A.comp A)
      _ ≤ d * 4 := mul_le_mul hcc' hAA (norm_nonneg _) hd
      _ = 4 * d := by ring
  have hquadratic : ‖c' • (A.comp A - B.comp B)‖ ≤ 8 * d := by
    calc
      ‖c' • (A.comp A - B.comp B)‖ ≤ |c'| * ‖A.comp A - B.comp B‖ := by
        simpa only [Real.norm_eq_abs] using
          ContinuousLinearMap.opNorm_smul_le c' (A.comp A - B.comp B)
      _ ≤ 1 * (8 * d) := mul_le_mul hc' hsq (norm_nonneg _) (by norm_num)
      _ = 8 * d := one_mul _
  have hsplit : rotationPolynomial A c - rotationPolynomial B c' =
      (A - B) + ((c - c') • A.comp A + c' • (A.comp A - B.comp B)) := by
    unfold rotationPolynomial
    rw [sub_smul, smul_sub]
    abel
  rw [hsplit]
  calc
    _ ≤ ‖A - B‖ + ‖(c - c') • A.comp A + c' • (A.comp A - B.comp B)‖ :=
      norm_add_le _ _
    _ ≤ ‖A - B‖ + (‖(c - c') • A.comp A‖ + ‖c' • (A.comp A - B.comp B)‖) :=
      add_le_add le_rfl (norm_add_le _ _)
    _ ≤ 2 * d + (4 * d + 8 * d) := add_le_add hAB (add_le_add hcoeff hquadratic)
    _ = 14 * d := by ring

lemma norm_rotation_sub_le (u v u' v' : E)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hu' : ‖u'‖ = 1) (hv' : ‖v'‖ = 1)
    (hκ : 0 ≤ ⟪u, v⟫_ℝ) (hκ' : 0 ≤ ⟪u', v'⟫_ℝ) :
    ‖rotation u v - rotation u' v'‖ ≤ 14 * (‖u - u'‖ + ‖v - v'‖) := by
  have hc' := inverse_one_add_bounds (⟪u', v'⟫_ℝ) hκ'
  apply norm_rotationPolynomial_sub_le
  · exact add_nonneg (norm_nonneg _) (norm_nonneg _)
  · exact norm_skew_le_two u v hu hv
  · exact norm_skew_le_two u' v' hu' hv'
  · exact norm_skew_sub_le u v u' v' hu hv hu' hv'
  · exact inverse_one_add_difference _ _ _ hκ hκ' (inner_sub_inner_le u v u' v' hv hu')
  · rw [abs_of_nonneg hc'.1]
    exact hc'.2

/-- Lipschitz dependence of the actual operators on two unit-vector families. -/
theorem rotation_lipschitzWith {X : Type uX} [PseudoMetricSpace X]
    (u v : X → E) {Ku Kv : ℝ≥0}
    (hu : ∀ x, ‖u x‖ = 1) (hv : ∀ x, ‖v x‖ = 1)
    (hκ : ∀ x, 0 ≤ ⟪u x, v x⟫_ℝ)
    (hLu : LipschitzWith Ku u) (hLv : LipschitzWith Kv v) :
    LipschitzWith (14 * (Ku + Kv)) (fun x => rotation (u x) (v x)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm]
  have hu' : ‖u x - u y‖ ≤ (Ku : ℝ) * dist x y := by
    simpa only [dist_eq_norm] using hLu.dist_le_mul x y
  have hv' : ‖v x - v y‖ ≤ (Kv : ℝ) * dist x y := by
    simpa only [dist_eq_norm] using hLv.dist_le_mul x y
  calc
    ‖rotation (u x) (v x) - rotation (u y) (v y)‖
        ≤ 14 * (‖u x - u y‖ + ‖v x - v y‖) :=
      norm_rotation_sub_le _ _ _ _ (hu x) (hv x) (hu y) (hv y) (hκ x) (hκ y)
    _ ≤ 14 * ((Ku : ℝ) * dist x y + (Kv : ℝ) * dist x y) :=
      mul_le_mul_of_nonneg_left (add_le_add hu' hv') (by norm_num)
    _ = (14 * (Ku + Kv) : ℝ≥0) * dist x y := by
      push_cast
      ring

theorem rotation_lipschitzWith_238 {X : Type uX} [PseudoMetricSpace X]
    (u v : X → E)
    (hu : ∀ x, ‖u x‖ = 1) (hv : ∀ x, ‖v x‖ = 1)
    (hκ : ∀ x, 0 ≤ ⟪u x, v x⟫_ℝ)
    (hLu : LipschitzWith 16 u) (hLv : LipschitzWith 1 v) :
    LipschitzWith 238 (fun x => rotation (u x) (v x)) := by
  convert rotation_lipschitzWith u v hu hv hκ hLu hLv using 1 ; norm_num

end ThompsonNonamenability.Analytic

end

end OAI

end
end

section
section
namespace OAI

/-!
# The explicit orthogonal operators along the actual curve
-/

noncomputable section

namespace ThompsonNonamenability.Analytic

open scoped InnerProductSpace

def R (t : ℝ) : Hilbert →L[ℝ] Hilbert := rotation (u t) (v t)

theorem R_apply_u (t : ℝ) : R t (u t) = v t :=
  rotation_apply_self _ _ (u_norm t) (v_norm t) (u_inner_v_nonneg t)

theorem R_inner (t : ℝ) (x y : Hilbert) :
    inner (𝕜 := ℝ) (R t x) (R t y) = inner (𝕜 := ℝ) x y :=
  rotation_inner _ _ (u_norm t) (v_norm t) (u_inner_v_nonneg t) x y

theorem R_norm (t : ℝ) (x : Hilbert) : ‖R t x‖ = ‖x‖ :=
  rotation_norm _ _ (u_norm t) (v_norm t) (u_inner_v_nonneg t) x

theorem R_perp (t : ℝ) (e : Hilbert) (he : inner (𝕜 := ℝ) e (u t) = 0) :
    inner (𝕜 := ℝ) (R t e) (v t) = 0 := by
  rw [← R_apply_u t, R_inner, he]

theorem R_early {t : ℝ} (ht : t ≤ 1) : R t = ContinuousLinearMap.id ℝ Hilbert := by
  rw [R, u_of_le_one ht, rotation_self]

theorem R_early_apply {t : ℝ} (ht : t ≤ 1) (e : Hilbert) : R t e = e := by
  rw [R_early ht]
  rfl

theorem lipschitzWith_R : LipschitzWith 238 R :=
  rotation_lipschitzWith_238 u v u_norm v_norm u_inner_v_nonneg
    lipschitzWith_u lipschitzWith_v

theorem R_sub_norm_le (s t : ℝ) (e : Hilbert) :
    ‖R t e - R s e‖ ≤ 238 * |t - s| * ‖e‖ := by
  have hop : ‖R t - R s‖ ≤ 238 * |t - s| := by
    simpa [dist_eq_norm, Real.norm_eq_abs] using
      lipschitzWith_R.dist_le_mul t s
  calc
    ‖R t e - R s e‖ = ‖(R t - R s) e‖ := rfl
    _ ≤ ‖R t - R s‖ * ‖e‖ := (R t - R s).le_opNorm e
    _ ≤ (238 * |t - s|) * ‖e‖ := mul_le_mul_of_nonneg_right hop (norm_nonneg e)

end ThompsonNonamenability.Analytic

end

end OAI

end
end

section
section
namespace OAI

/-!
# Finite-region uniform separation

The generic results below separate the compactness and scalar estimates from
the concrete curve calculations. The actual analytic curve must supply every
listed identity and inequality before this result is used in the tube theorem.
-/

noncomputable section


namespace ThompsonNonamenability.Analytic

open Set

theorem exists_uniform_sep_on_square
    {H : Type uH} [NormedAddCommGroup H]
    (γ : ℝ → H) (hcont : Continuous γ) (hinj : Function.Injective γ)
    (d : ℝ) (hd : 0 < d) :
    ∃ μ : ℝ, 0 < μ ∧
      ∀ s ∈ Icc (-4 : ℝ) 5,
      ∀ t ∈ Icc (-4 : ℝ) 5,
        d ≤ t - s → μ ≤ ‖γ t - γ s‖ := by
  let C : Set (ℝ × ℝ) :=
    (Icc (-4 : ℝ) 5 ×ˢ Icc (-4 : ℝ) 5) ∩ {p | d ≤ p.2 - p.1}
  have hclosed : IsClosed {p : ℝ × ℝ | d ≤ p.2 - p.1} :=
    isClosed_le continuous_const (continuous_snd.sub continuous_fst)
  have hcompact : IsCompact C :=
    ((isCompact_Icc : IsCompact (Icc (-4 : ℝ) 5)).prod isCompact_Icc).inter_right
      hclosed
  have hcontinuous : Continuous (fun p : ℝ × ℝ => ‖γ p.2 - γ p.1‖) :=
    ((hcont.comp continuous_snd).sub (hcont.comp continuous_fst)).norm
  have hpositive : ∀ p ∈ C, 0 < ‖γ p.2 - γ p.1‖ := by
    intro p hp
    apply norm_pos_iff.mpr
    apply sub_ne_zero.mpr
    intro heq
    have hparam : p.2 = p.1 := hinj heq
    have hgap : d ≤ p.2 - p.1 := hp.2
    rw [hparam, sub_self] at hgap
    exact (not_le_of_gt hd) hgap
  obtain ⟨μ, hμ, hbound⟩ := hcompact.exists_forall_le'
    hcontinuous.continuousOn hpositive
  refine ⟨μ, hμ, ?_⟩
  intro s hs t ht hgap
  exact hbound (s, t) ⟨⟨hs, ht⟩, hgap⟩

theorem uniform_separation_of_five_regions
    {H : Type uH} [NormedAddCommGroup H]
    (γ : ℝ → H) (hcont : Continuous γ) (hinj : Function.Injective γ)
    (hline : ∀ s t : ℝ, s ≤ t → t ≤ 1 → ‖γ t - γ s‖ = (t - s) / 8)
    (hnegative : ∀ s t : ℝ, s ≤ -4 → 1 < t → 3 / 16 ≤ ‖γ t - γ s‖)
    (htail : ∀ s t : ℝ, 3 ≤ s → s ≤ t →
      ‖γ t - γ s‖ ^ 2 = 2 * (5 / 16 : ℝ) ^ 2 * (1 - sinc (t - s)))
    (hmixed : ∀ s t : ℝ, s ≤ 3 → 5 ≤ t →
      3 * (5 / 16 : ℝ) ^ 2 / 4 ≤ ‖γ t - γ s‖ ^ 2)
    (d : ℝ) (hd : 0 < d) :
    ∃ η : ℝ, 0 < η ∧ ∀ s t : ℝ, d ≤ |t - s| → η ≤ ‖γ t - γ s‖ := by
  obtain ⟨ε, hε, hεhalf, hsinc⟩ := exists_uniform_sinc_gap d hd
  obtain ⟨μ, hμ, hcompact⟩ := exists_uniform_sep_on_square γ hcont hinj d hd
  let η : ℝ := min (d / 8) (min (3 / 16) (min ((5 / 16) * ε) (min (5 / 32) μ)))
  have hηpos : 0 < η := by
    dsimp [η]
    exact lt_min (div_pos hd (by norm_num))
      (lt_min (by norm_num) (lt_min (mul_pos (by norm_num) hε)
        (lt_min (by norm_num) hμ)))
  have hηline : η ≤ d / 8 := min_le_left _ _
  have hηneg : η ≤ 3 / 16 := (min_le_right _ _).trans (min_le_left _ _)
  have hηtail : η ≤ (5 / 16) * ε :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hηmixed : η ≤ 5 / 32 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _)))
  have hηcompact : η ≤ μ :=
    (min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_right _ _)))
  have hordered : ∀ s t : ℝ, d ≤ t - s → η ≤ ‖γ t - γ s‖ := by
    intro s t hgap
    have hst : s ≤ t := by linarith
    by_cases ht1 : t ≤ 1
    · rw [hline s t hst ht1]
      exact hηline.trans (by linarith)
    have ht1' : 1 < t := lt_of_not_ge ht1
    by_cases hsneg : s ≤ -4
    · exact hηneg.trans (hnegative s t hsneg ht1')
    by_cases hs3 : 3 ≤ s
    · have hsq : ((5 / 16 : ℝ) * ε) ^ 2 ≤ ‖γ t - γ s‖ ^ 2 := by
        rw [htail s t hs3 hst]
        have hepssq : ε ^ 2 ≤ 2 * ε := by
          nlinarith [mul_le_mul_of_nonneg_right hεhalf hε.le]
        have hgap' := hsinc (t - s) hgap
        nlinarith
      have hlow : (5 / 16 : ℝ) * ε ≤ ‖γ t - γ s‖ :=
        (sq_le_sq₀ (mul_nonneg (by norm_num) hε.le) (norm_nonneg _)).mp hsq
      exact hηtail.trans hlow
    by_cases ht5 : 5 ≤ t
    · have hsq : (5 / 32 : ℝ) ^ 2 ≤ ‖γ t - γ s‖ ^ 2 := by
        have hm := hmixed s t (le_of_not_ge hs3) ht5
        nlinarith
      have hlow : (5 / 32 : ℝ) ≤ ‖γ t - γ s‖ :=
        (sq_le_sq₀ (by norm_num) (norm_nonneg _)).mp hsq
      exact hηmixed.trans hlow
    · exact hηcompact.trans (hcompact s ⟨by linarith, by linarith⟩
        t ⟨by linarith, by linarith⟩ hgap)
  refine ⟨η, hηpos, ?_⟩
  intro s t hgap
  by_cases hst : s ≤ t
  · exact hordered s t (by simpa [abs_of_nonneg (sub_nonneg.mpr hst)] using hgap)
  · have hts : t ≤ s := (lt_of_not_ge hst).le
    have hgap' : d ≤ s - t := by
      simpa [abs_of_nonpos (sub_nonpos.mpr hts), neg_sub] using hgap
    simpa only [norm_sub_rev] using hordered t s hgap'

end ThompsonNonamenability.Analytic

end

end OAI

end
end

section
section
namespace OAI

/-!
# Uniform separation of the actual Hilbert-space curve

Every premise of the finite-region separation theorem is proved here from the
literal scalar profiles and the oscillator inner-product identity. In
particular no separation or injectivity property of the curve is assumed.
-/

noncomputable section

namespace ThompsonNonamenability.Analytic

open Set

theorem gamma_sub_norm_of_le_one (s t : ℝ) (hst : s ≤ t) (ht : t ≤ 1) :
    ‖gamma t - gamma s‖ = (t - s) / 8 := by
  rw [gamma_of_le_one ht, gamma_of_le_one (hst.trans ht), ← sub_smul,
    norm_smul, Real.norm_eq_abs, wave_norm, mul_one]
  have hdiv : t / 8 - s / 8 = (t - s) / 8 := by ring
  rw [hdiv, abs_of_nonneg (div_nonneg (sub_nonneg.mpr hst) (by norm_num))]

theorem theta_lt_of_lt_of_one_lt {s t : ℝ} (hst : s < t) (ht : 1 < t) :
    theta s < theta t := by
  by_cases hs : s ≤ 1
  · have hstrict := theta_strictMonoOn
      (show (1 : ℝ) ∈ Ici (1 : ℝ) from le_refl (1 : ℝ))
      (show t ∈ Ici (1 : ℝ) from ht.le) ht
    simpa only [theta_of_le_one hs, theta_of_le_one (le_refl (1 : ℝ))] using hstrict
  · exact theta_strictMonoOn (le_of_not_ge hs) ht.le hst

theorem gamma_sub_norm_pos {s t : ℝ} (hst : s < t) : 0 < ‖gamma t - gamma s‖ := by
  by_cases ht : t ≤ 1
  · rw [gamma_sub_norm_of_le_one s t hst.le ht]
    exact div_pos (sub_pos.mpr hst) (by norm_num)
  have ht' : 1 < t := lt_of_not_ge ht
  have ha : 0 < a t := by linarith [a_lower_of_one_le ht'.le]
  have hgap : 0 < theta t - theta s := sub_pos.mpr (theta_lt_of_lt_of_one_lt hst ht')
  have hk : |sinc (theta t - theta s)| < 1 := abs_sinc_lt_one (ne_of_gt hgap)
  have hk2 : sinc (theta t - theta s) ^ 2 < 1 := by
    have h := (sq_lt_sq₀ (abs_nonneg (sinc (theta t - theta s)))
      (by norm_num : (0 : ℝ) ≤ 1)).2 hk
    simpa only [sq_abs, one_pow] using h
  have hpositive : 0 < (a t) ^ 2 * (1 - sinc (theta t - theta s) ^ 2) :=
    mul_pos (sq_pos_of_pos ha) (sub_pos.mpr hk2)
  have hnonneg := sq_nonneg (a s - a t * sinc (theta t - theta s))
  have hformula := gamma_sub_norm_sq s t
  have hsq : 0 < ‖gamma t - gamma s‖ ^ 2 := by nlinarith
  exact lt_of_le_of_ne (norm_nonneg _) (Ne.symm (sq_pos_iff.mp hsq))

theorem gamma_injective : Function.Injective gamma := by
  intro s t heq
  by_contra hne
  rcases lt_or_gt_of_ne hne with hst | hts
  · have hpositive := gamma_sub_norm_pos hst
    exact (ne_of_gt hpositive) (by simp only [heq, sub_self, norm_zero])
  · have hpositive := gamma_sub_norm_pos hts
    exact (ne_of_gt hpositive) (by simp only [heq, sub_self, norm_zero])

theorem gamma_sub_norm_ge_of_far_negative (s t : ℝ) (hs : s ≤ -4) (ht : 1 < t) :
    3 / 16 ≤ ‖gamma t - gamma s‖ := by
  have hsbound : (1 / 2 : ℝ) ≤ ‖gamma s‖ := by
    rw [gamma_norm, a_of_le_two (by linarith), abs_of_nonpos (by linarith)]
    linarith
  have htbound : ‖gamma t‖ ≤ 5 / 16 := by
    have hapos : 0 ≤ a t := by linarith [a_lower_of_one_le ht.le]
    rw [gamma_norm, abs_of_nonneg hapos]
    exact a_le_five_sixteenths t
  have hreverse : ‖gamma s‖ - ‖gamma t‖ ≤ ‖gamma t - gamma s‖ := by
    simpa only [norm_sub_rev] using norm_sub_norm_le (gamma s) (gamma t)
  linarith

theorem gamma_sub_norm_sq_tail (s t : ℝ) (hs : 3 ≤ s) (hst : s ≤ t) :
    ‖gamma t - gamma s‖ ^ 2 = 2 * (5 / 16 : ℝ) ^ 2 * (1 - sinc (t - s)) := by
  rw [gamma_sub_norm_sq, a_of_three_le hs, a_of_three_le (hs.trans hst),
    theta_of_two_le (by linarith : 2 ≤ t), theta_of_two_le (by linarith : 2 ≤ s)]
  have hgap : (t - 3 / 2) - (s - 3 / 2) = t - s := by ring
  rw [hgap]
  ring

theorem gamma_sub_norm_sq_ge_of_cross_tail (s t : ℝ) (hs : s ≤ 3) (ht : 5 ≤ t) :
    3 * (5 / 16 : ℝ) ^ 2 / 4 ≤ ‖gamma t - gamma s‖ ^ 2 := by
  have htheta_s : theta s ≤ 3 / 2 := by
    calc
      theta s ≤ theta 3 := theta_monotone hs
      _ = 3 / 2 := by rw [theta_of_two_le (by norm_num : (2 : ℝ) ≤ 3)]; norm_num
  have htheta_t : 7 / 2 ≤ theta t := by
    rw [theta_of_two_le (by linarith)]
    linarith
  have hgap : 2 ≤ theta t - theta s := by linarith
  have habs := abs_sinc_le_half_of_two_le hgap
  have hklow := (abs_le.mp habs).1
  have hkhi := (abs_le.mp habs).2
  have hproduct : 0 ≤ (sinc (theta t - theta s) + 1 / 2) *
      (1 / 2 - sinc (theta t - theta s)) := mul_nonneg (by linarith) (by linarith)
  have hk2 : sinc (theta t - theta s) ^ 2 ≤ 1 / 4 := by nlinarith
  rw [gamma_sub_norm_sq, a_of_three_le (by linarith : 3 ≤ t)]
  nlinarith [sq_nonneg (a s - (5 / 16 : ℝ) * sinc (theta t - theta s))]

theorem gamma_uniform_separation (d : ℝ) (hd : 0 < d) :
    ∃ η : ℝ, 0 < η ∧ ∀ s t : ℝ, d ≤ |t - s| → η ≤ ‖gamma t - gamma s‖ :=
  uniform_separation_of_five_regions gamma continuous_gamma gamma_injective
    gamma_sub_norm_of_le_one gamma_sub_norm_ge_of_far_negative gamma_sub_norm_sq_tail
    gamma_sub_norm_sq_ge_of_cross_tail d hd

end ThompsonNonamenability.Analytic

end

end OAI

end
end

section
section
namespace OAI

noncomputable section


namespace ThompsonNonamenability.Analytic

open Set
open scoped InnerProductSpace

variable (E : Type uE) [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Differential and separation data at the fixed parameter scale `1 / 32`. -/
structure RegularCurveData where
  curve : ℝ → E
  velocity : ℝ → E
  tangent : ℝ → E
  hasDerivAt : ∀ t, HasDerivAt curve (velocity t) t
  norm_tangent : ∀ t, ‖tangent t‖ = 1
  velocity_eq : ∀ t, velocity t = ‖velocity t‖ • tangent t
  speed_lower : ∀ t, (1 / 8 : ℝ) ≤ ‖velocity t‖
  velocity_lipschitz : ∀ s t, ‖velocity t - velocity s‖ ≤ |t - s|
  tangent_lipschitz : ∀ s t, ‖tangent t - tangent s‖ ≤ 16 * |t - s|
  separation : ℝ
  separation_pos : 0 < separation
  separated : ∀ s t, (1 / 32 : ℝ) ≤ |t - s| →
    separation ≤ ‖curve t - curve s‖

variable {E}

namespace RegularCurveData

variable (C : RegularCurveData E)

theorem continuous_curve : Continuous C.curve :=
  continuous_iff_continuousAt.mpr fun t => (C.hasDerivAt t).continuousAt

/-- A radius with slack in both the separation and curvature estimates. -/
def rho : ℝ := min (1 / 1024) (C.separation / 8)

theorem rho_pos : 0 < C.rho := by
  exact lt_min (by norm_num) (div_pos C.separation_pos (by norm_num))

theorem rho_le : C.rho ≤ 1 / 1024 := min_le_left _ _

theorem rho_le_separation : C.rho ≤ C.separation / 8 := min_le_right _ _

theorem four_rho_lt_separation : 4 * C.rho < C.separation := by
  have := C.rho_le_separation
  have := C.separation_pos
  linarith

theorem tangent_error_small : C.rho * 16 < 1 / 32 := by
  have := C.rho_le
  linarith

/-- The actual open metric tube around the range of the curve. -/
def tube : Set E := {x | Metric.infDist x (range C.curve) < C.rho}

theorem range_nonempty : (range C.curve).Nonempty := ⟨C.curve 0, mem_range_self 0⟩

end RegularCurveData

end ThompsonNonamenability.Analytic

end

end OAI

end
end

section
section
namespace OAI

/-!
# Global nearest points obtained by compact parameter minimization

No properness of the ambient inner-product space is required. Separation of
the curve confines minimization to a compact interval in its real parameter.
-/

noncomputable section


namespace ThompsonNonamenability.Analytic.RegularCurveData

open Set Filter
open scoped InnerProductSpace Topology

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable (C : RegularCurveData E)

/-- The predicate of being a global nearest parameter for the actual curve. -/
def IsNearest (x : E) (s : ℝ) : Prop :=
  ∀ t : ℝ, ‖x - C.curve s‖ ≤ ‖x - C.curve t‖

/-- The separation estimate makes the residual strictly larger away from a
compact interval around any initial tube witness. -/
theorem residual_gt_of_far {x : E} {s t : ℝ}
    (hs : ‖x - C.curve s‖ < C.rho) (hst : (1 / 32 : ℝ) ≤ |t - s|) :
    3 * C.rho < ‖x - C.curve t‖ := by
  have hsep := C.separated s t hst
  have htri : ‖C.curve t - C.curve s‖ ≤
      ‖x - C.curve t‖ + ‖x - C.curve s‖ := by
    calc
      ‖C.curve t - C.curve s‖ ≤
          ‖C.curve t - x‖ + ‖x - C.curve s‖ := by
        simpa only [dist_eq_norm] using dist_triangle (C.curve t) x (C.curve s)
      _ = ‖x - C.curve t‖ + ‖x - C.curve s‖ := by
        rw [norm_sub_rev (C.curve t) x]
  have := C.four_rho_lt_separation
  linarith

/-- A tube point has a global nearest parameter, attained by minimizing on a
compact interval of real parameters. -/
theorem nearest_exists (x : E) (hx : x ∈ C.tube) :
    ∃ s : ℝ, C.IsNearest x s ∧ ‖x - C.curve s‖ < C.rho := by
  obtain ⟨z, ⟨t₀, rfl⟩, ht₀⟩ :=
    (Metric.infDist_lt_iff C.range_nonempty).mp hx
  have ht₀' : ‖x - C.curve t₀‖ < C.rho := by
    simpa only [dist_eq_norm] using ht₀
  have ht₀mem : t₀ ∈ Icc (t₀ - 1 / 32) (t₀ + 1 / 32) := by
    constructor <;> linarith
  have hcont : Continuous (fun t : ℝ => ‖x - C.curve t‖) :=
    (continuous_const.sub C.continuous_curve).norm
  obtain ⟨s, hs, hmin⟩ := isCompact_Icc.exists_isMinOn ⟨t₀, ht₀mem⟩
    hcont.continuousOn
  have hsclose : ‖x - C.curve s‖ < C.rho :=
    lt_of_le_of_lt (hmin ht₀mem) ht₀'
  refine ⟨s, ?_, hsclose⟩
  intro t
  by_cases ht : t ∈ Icc (t₀ - 1 / 32) (t₀ + 1 / 32)
  · exact hmin ht
  · have hfar : (1 / 32 : ℝ) ≤ |t - t₀| := by
      by_contra h
      have hnear := abs_lt.mp (lt_of_not_ge h)
      exact ht ⟨by linarith [hnear.1], by linarith [hnear.2]⟩
    have hlarge := C.residual_gt_of_far ht₀' hfar
    have := C.rho_pos
    linarith

/-- Every global minimizer has exactly the distance-to-range residual. -/
theorem nearest_norm_eq_infDist {x : E} {s : ℝ} (hs : C.IsNearest x s) :
    ‖x - C.curve s‖ = Metric.infDist x (range C.curve) := by
  apply le_antisymm
  · apply (Metric.le_infDist C.range_nonempty).mpr
    rintro y ⟨t, rfl⟩
    simpa only [dist_eq_norm] using hs t
  · simpa only [dist_eq_norm] using
      Metric.infDist_le_dist_of_mem (x := x) (mem_range_self s)

/-- Differentiating the squared residual at its global minimum proves
orthogonality to the tangent. -/
theorem nearest_perp_tangent {x : E} {s : ℝ} (hs : C.IsNearest x s) :
    ⟪x - C.curve s, C.tangent s⟫_ℝ = 0 := by
  have hsquare : IsMinOn (fun t : ℝ => ‖x - C.curve t‖ ^ 2) univ s := by
    apply isMinOn_univ_iff.mpr
    intro t
    exact pow_le_pow_left₀ (norm_nonneg _) (hs t) 2
  have hlocal : IsLocalMin (fun t : ℝ => ‖x - C.curve t‖ ^ 2) s :=
    hsquare.isLocalMin (by simp)
  have hderiv : HasDerivAt (fun t : ℝ => ‖x - C.curve t‖ ^ 2)
      (2 * ⟪x - C.curve s, -C.velocity s⟫_ℝ) s :=
    ((C.hasDerivAt s).const_sub x).norm_sq
  have hzero := hlocal.hasDerivAt_eq_zero hderiv
  have hspeed : ‖C.velocity s‖ ≠ 0 := by
    have := C.speed_lower s
    linarith
  rw [inner_neg_right, C.velocity_eq s, real_inner_smul_right] at hzero
  have hproduct : ‖C.velocity s‖ * ⟪x - C.curve s, C.tangent s⟫_ℝ = 0 := by
    linarith
  exact (mul_eq_zero.mp hproduct).resolve_left hspeed

end ThompsonNonamenability.Analytic.RegularCurveData

end

end OAI

end
end

section
section
namespace OAI

/-!
# A quantitative lower bound for tangent projections

On a parameter interval of length at most `1 / 32`, the velocity has inner
product at least `3 / 32` with the tangent at either prescribed endpoint.
The scalar mean value theorem then bounds the projected chord from below.
-/

noncomputable section


namespace ThompsonNonamenability.Analytic

open Set
open scoped InnerProductSpace

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

namespace RegularCurveData

variable (C : RegularCurveData E)

theorem velocity_inner_tangent (s : ℝ) :
    inner (𝕜 := ℝ) (C.velocity s) (C.tangent s) = ‖C.velocity s‖ := by
  calc
    inner (𝕜 := ℝ) (C.velocity s) (C.tangent s) =
        inner (𝕜 := ℝ) (‖C.velocity s‖ • C.tangent s) (C.tangent s) :=
      congrArg (fun v => inner (𝕜 := ℝ) v (C.tangent s)) (C.velocity_eq s)
    _ = ‖C.velocity s‖ := by
      rw [real_inner_smul_left, real_inner_self_eq_norm_sq, C.norm_tangent]
      simp

/-- The derivative of projection onto the fixed tangent at `s` stays positive
throughout the prescribed parameter scale. -/
theorem velocity_tangent_lower (s t : ℝ) (hst : |t - s| ≤ 1 / 32) :
    (3 / 32 : ℝ) ≤ inner (𝕜 := ℝ) (C.velocity t) (C.tangent s) := by
  have hinner := abs_real_inner_le_norm (C.velocity t - C.velocity s) (C.tangent s)
  rw [C.norm_tangent, mul_one, inner_sub_left, C.velocity_inner_tangent] at hinner
  have herror : |inner (𝕜 := ℝ) (C.velocity t) (C.tangent s) - ‖C.velocity s‖| ≤
      |t - s| := hinner.trans (C.velocity_lipschitz s t)
  have hlo := (abs_le.mp herror).1
  have hspeed := C.speed_lower s
  linarith

/-- The chord's projection onto the tangent at its first parameter controls
parameter distance. The tangent remains fixed at `s` for either order of `s`
and `t`. -/
theorem tangent_projection_lower (s t : ℝ) (hst : |t - s| ≤ 1 / 32) :
    (3 / 32 : ℝ) * |t - s| ≤
      |inner (𝕜 := ℝ) (C.curve t - C.curve s) (C.tangent s)| := by
  let f : ℝ → ℝ := fun u => inner (𝕜 := ℝ) (C.curve u) (C.tangent s)
  let f' : ℝ → ℝ := fun u => inner (𝕜 := ℝ) (C.velocity u) (C.tangent s)
  have hf : ∀ u, HasDerivAt f (f' u) u := by
    intro u
    simpa only [f, f', inner_zero_right, zero_add] using
      (C.hasDerivAt u).inner ℝ (hasDerivAt_const u (C.tangent s))
  have hfc : Continuous f :=
    continuous_iff_continuousAt.mpr fun u => (hf u).continuousAt
  rw [inner_sub_left]
  change (3 / 32 : ℝ) * |t - s| ≤ |f t - f s|
  rcases lt_trichotomy s t with hlt | heq | hlt
  · obtain ⟨u, hu, hdu⟩ :=
      exists_hasDerivAt_eq_slope f f' hlt hfc.continuousOn (fun u _ => hf u)
    have hus : |u - s| ≤ 1 / 32 := by
      apply abs_le.mpr
      constructor <;> linarith [(abs_le.mp hst).1, (abs_le.mp hst).2, hu.1, hu.2]
    have hlo : (3 / 32 : ℝ) ≤ f' u := C.velocity_tangent_lower s u hus
    rw [hdu] at hlo
    have hgrow : (3 / 32 : ℝ) * (t - s) ≤ f t - f s :=
      (le_div_iff₀ (sub_pos.mpr hlt)).mp hlo
    rw [abs_of_nonneg (sub_nonneg.mpr hlt.le)]
    exact hgrow.trans (le_abs_self _)
  · subst t
    simp
  · obtain ⟨u, hu, hdu⟩ :=
      exists_hasDerivAt_eq_slope f f' hlt hfc.continuousOn (fun u _ => hf u)
    have hus : |u - s| ≤ 1 / 32 := by
      apply abs_le.mpr
      constructor <;> linarith [(abs_le.mp hst).1, (abs_le.mp hst).2, hu.1, hu.2]
    have hlo : (3 / 32 : ℝ) ≤ f' u := C.velocity_tangent_lower s u hus
    rw [hdu] at hlo
    have hgrow : (3 / 32 : ℝ) * (s - t) ≤ f s - f t :=
      (le_div_iff₀ (sub_pos.mpr hlt)).mp hlo
    rw [abs_sub_comm t s, abs_of_nonneg (sub_nonneg.mpr hlt.le)]
    refine hgrow.trans ?_
    calc
      f s - f t = -(f t - f s) := (neg_sub _ _).symm
      _ ≤ |f t - f s| := neg_le_abs _

end RegularCurveData

end ThompsonNonamenability.Analytic

end

end OAI

end
end

section
section
namespace OAI

/-!
# Comparing parameters of nearby normal points

Separation first puts the parameters in the range of the tangent projection
estimate. Orthogonality then bounds the remaining projection error by the
variation of the tangent. No nearest-point selection is used here.
-/

noncomputable section


namespace ThompsonNonamenability.Analytic

open scoped InnerProductSpace

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

namespace RegularCurveData

variable (C : RegularCurveData E)

/-- Normal parameters of two nearby points in the tube satisfy a uniform
comparison estimate. -/
theorem parameter_comparison (x y : E) (s t : ℝ)
    (hx : ‖x - C.curve s‖ < C.rho) (hy : ‖y - C.curve t‖ < C.rho)
    (hxy : ‖x - y‖ < C.rho)
    (hperp_x : inner (𝕜 := ℝ) (x - C.curve s) (C.tangent s) = 0)
    (hperp_y : inner (𝕜 := ℝ) (y - C.curve t) (C.tangent t) = 0) :
    |t - s| ≤ 16 * ‖x - y‖ := by
  have hcurve : ‖C.curve t - C.curve s‖ < 3 * C.rho := by
    have h₁ := norm_sub_le_norm_sub_add_norm_sub (C.curve t) y x
    have h₂ := norm_sub_le_norm_sub_add_norm_sub (C.curve t) x (C.curve s)
    rw [norm_sub_rev (C.curve t) y, norm_sub_rev y x] at h₁
    linarith
  have hst : |t - s| ≤ 1 / 32 := by
    apply le_of_not_gt
    intro hlarge
    have hsep := C.separated s t (le_of_lt hlarge)
    have hrho := C.rho_pos
    have hfour := C.four_rho_lt_separation
    linarith
  have htan : ‖C.tangent s - C.tangent t‖ ≤ 16 * |t - s| := by
    simpa only [norm_sub_rev (C.tangent t) (C.tangent s)] using
      C.tangent_lipschitz s t
  have herror :
      |inner (𝕜 := ℝ) (y - C.curve t) (C.tangent s - C.tangent t)| ≤
        C.rho * 16 * |t - s| := by
    calc
      |inner (𝕜 := ℝ) (y - C.curve t) (C.tangent s - C.tangent t)|
          ≤ ‖y - C.curve t‖ * ‖C.tangent s - C.tangent t‖ :=
        abs_real_inner_le_norm _ _
      _ ≤ ‖y - C.curve t‖ * (16 * |t - s|) :=
        mul_le_mul_of_nonneg_left htan (norm_nonneg _)
      _ ≤ C.rho * (16 * |t - s|) :=
        mul_le_mul_of_nonneg_right (le_of_lt hy) (by positivity)
      _ = C.rho * 16 * |t - s| := (mul_assoc _ _ _).symm
  have hpoint : |inner (𝕜 := ℝ) (y - x) (C.tangent s)| ≤ ‖x - y‖ := by
    calc
      |inner (𝕜 := ℝ) (y - x) (C.tangent s)| ≤ ‖y - x‖ * ‖C.tangent s‖ :=
        abs_real_inner_le_norm _ _
      _ = ‖x - y‖ := by rw [C.norm_tangent, mul_one, norm_sub_rev]
  have hidentity :
      inner (𝕜 := ℝ) (C.curve t - C.curve s) (C.tangent s) =
        inner (𝕜 := ℝ) (y - x) (C.tangent s) -
          inner (𝕜 := ℝ) (y - C.curve t) (C.tangent s - C.tangent t) := by
    simp only [inner_sub_left, inner_sub_right] at hperp_x hperp_y ⊢
    linarith
  have hupper :
      |inner (𝕜 := ℝ) (C.curve t - C.curve s) (C.tangent s)| ≤
        ‖x - y‖ + C.rho * 16 * |t - s| := by
    rw [hidentity]
    calc
      |inner (𝕜 := ℝ) (y - x) (C.tangent s) -
          inner (𝕜 := ℝ) (y - C.curve t) (C.tangent s - C.tangent t)|
          ≤ |inner (𝕜 := ℝ) (y - x) (C.tangent s)| +
            |inner (𝕜 := ℝ) (y - C.curve t) (C.tangent s - C.tangent t)| := by
        simpa only [sub_zero, zero_sub, abs_neg] using
          abs_sub_le (inner (𝕜 := ℝ) (y - x) (C.tangent s)) 0
            (inner (𝕜 := ℝ) (y - C.curve t) (C.tangent s - C.tangent t))
      _ ≤ ‖x - y‖ + C.rho * 16 * |t - s| := add_le_add hpoint herror
  have hlower := C.tangent_projection_lower s t hst
  have hsmall : C.rho * 16 * |t - s| ≤ (1 / 32) * |t - s| :=
    mul_le_mul_of_nonneg_right (le_of_lt C.tangent_error_small) (abs_nonneg _)
  linarith

end RegularCurveData

end ThompsonNonamenability.Analytic

end

end OAI

end
end

section
section
namespace OAI

/-!
# The actual nearest-point parameter on a quantitative curve tube

Compact minimization, stationarity, and the tangent comparison establish
existence and uniqueness before the nearest parameter is selected.
-/

noncomputable section


namespace ThompsonNonamenability.Analytic.RegularCurveData

open Set
open scoped InnerProductSpace

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable (C : RegularCurveData E)

/-- The unique global nearest parameter, selected after proving attainment. -/
def parameter (x : C.tube) : ℝ :=
  Classical.choose (C.nearest_exists x x.property)

theorem parameter_isNearest (x : C.tube) : C.IsNearest x (C.parameter x) :=
  (Classical.choose_spec (C.nearest_exists x x.property)).1

/-- The actual normal residual in the ambient inner-product space. -/
def residual (x : C.tube) : E := (x : E) - C.curve (C.parameter x)

theorem curve_add_residual (x : C.tube) :
    C.curve (C.parameter x) + C.residual x = (x : E) := by
  simp [residual]

theorem residual_norm (x : C.tube) :
    ‖C.residual x‖ = Metric.infDist (x : E) (range C.curve) :=
  C.nearest_norm_eq_infDist (C.parameter_isNearest x)

theorem residual_norm_lt (x : C.tube) : ‖C.residual x‖ < C.rho := by
  rw [C.residual_norm]
  exact x.property

theorem residual_perp_u (x : C.tube) :
    ⟪C.residual x, C.tangent (C.parameter x)⟫_ℝ = 0 :=
  C.nearest_perp_tangent (C.parameter_isNearest x)

theorem parameter_local_bound16 (x y : C.tube)
    (hxy : ‖(x : E) - (y : E)‖ < C.rho) :
    |C.parameter x - C.parameter y| ≤ 16 * ‖(x : E) - (y : E)‖ := by
  rw [abs_sub_comm (C.parameter x) (C.parameter y)]
  exact C.parameter_comparison x y (C.parameter x) (C.parameter y)
    (C.residual_norm_lt x) (C.residual_norm_lt y) hxy
    (C.residual_perp_u x) (C.residual_perp_u y)

end ThompsonNonamenability.Analytic.RegularCurveData

end

end OAI

end
end

section
section
namespace OAI

/-!
# Scalar cutoffs for the Hilbert displacement construction

The inner cutoff `beta` is one through radius `ρ / 4` and vanishes from
`ρ / 2`. The outer cutoff `chi` is one through radius `ρ / 2` and vanishes
from `ρ`. Both formulas take values in `[0, 1]` even outside this domain.
-/

noncomputable section

namespace ThompsonNonamenability.Analytic

/-- The cutoff supported inside the half-radius ball. -/
def beta (ρ r : ℝ) : ℝ := min 1 (max 0 (2 - 4 * r / ρ))

/-- The cutoff supported inside the full-radius ball. -/
def chi (ρ r : ℝ) : ℝ := min 1 (max 0 (2 - 2 * r / ρ))

theorem beta_nonneg (ρ r : ℝ) : 0 ≤ beta ρ r :=
  le_min zero_le_one (le_max_left _ _)

theorem beta_le_one (ρ r : ℝ) : beta ρ r ≤ 1 :=
  min_le_left _ _

theorem chi_nonneg (ρ r : ℝ) : 0 ≤ chi ρ r :=
  le_min zero_le_one (le_max_left _ _)

theorem chi_le_one (ρ r : ℝ) : chi ρ r ≤ 1 :=
  min_le_left _ _

theorem beta_eq_one {ρ : ℝ} (hρ : 0 < ρ) (r : ℝ) (hr : r ≤ ρ / 4) :
    beta ρ r = 1 := by
  have hdiv : 4 * r / ρ ≤ 1 := (div_le_iff₀ hρ).2 (by nlinarith)
  have harg : 1 ≤ 2 - 4 * r / ρ := by linarith
  exact min_eq_left (harg.trans (le_max_right _ _))

theorem beta_eq_zero {ρ : ℝ} (hρ : 0 < ρ) (r : ℝ) (hr : ρ / 2 ≤ r) :
    beta ρ r = 0 := by
  have hdiv : 2 ≤ 4 * r / ρ := (le_div_iff₀ hρ).2 (by nlinarith)
  have harg : 2 - 4 * r / ρ ≤ 0 := by linarith
  simp only [beta, max_eq_left harg, min_eq_right zero_le_one]

theorem chi_eq_one {ρ : ℝ} (hρ : 0 < ρ) (r : ℝ) (hr : r ≤ ρ / 2) :
    chi ρ r = 1 := by
  have hdiv : 2 * r / ρ ≤ 1 := (div_le_iff₀ hρ).2 (by nlinarith)
  have harg : 1 ≤ 2 - 2 * r / ρ := by linarith
  exact min_eq_left (harg.trans (le_max_right _ _))

private theorem clamp_abs_sub_le (x y : ℝ) :
    |min 1 (max 0 x) - min 1 (max 0 y)| ≤ |x - y| := by
  have hmin : |min 1 (max 0 x) - min 1 (max 0 y)| ≤
      |max 0 x - max 0 y| := by
    simpa only [sub_self, abs_zero, max_eq_right (abs_nonneg (max (0 : ℝ) x - max 0 y))] using
      abs_min_sub_min_le_max (1 : ℝ) (max 0 x) 1 (max 0 y)
  have hmax : |max 0 x - max 0 y| ≤ |x - y| := by
    rw [max_comm 0 x, max_comm 0 y]
    exact abs_max_sub_max_le_abs x y 0
  exact hmin.trans hmax

theorem beta_abs_sub_le {ρ : ℝ} (hρ : 0 < ρ) (r s : ℝ) :
    |beta ρ r - beta ρ s| ≤ (4 / ρ) * |r - s| := by
  have h := clamp_abs_sub_le (2 - 4 * r / ρ) (2 - 4 * s / ρ)
  have heq : (2 - 4 * r / ρ) - (2 - 4 * s / ρ) =
      -(4 / ρ * (r - s)) := by ring
  have hc : 0 ≤ (4 : ℝ) / ρ := div_nonneg (by norm_num) hρ.le
  rw [heq, abs_neg, abs_mul, abs_of_nonneg hc] at h
  exact h

theorem chi_abs_sub_le {ρ : ℝ} (hρ : 0 < ρ) (r s : ℝ) :
    |chi ρ r - chi ρ s| ≤ (2 / ρ) * |r - s| := by
  have h := clamp_abs_sub_le (2 - 2 * r / ρ) (2 - 2 * s / ρ)
  have heq : (2 - 2 * r / ρ) - (2 - 2 * s / ρ) =
      -(2 / ρ * (r - s)) := by ring
  have hc : 0 ≤ (2 : ℝ) / ρ := div_nonneg (by norm_num) hρ.le
  rw [heq, abs_neg, abs_mul, abs_of_nonneg hc] at h
  exact h

theorem beta_le_chi {ρ : ℝ} (hρ : 0 < ρ) (r : ℝ) (hr : 0 ≤ r) :
    beta ρ r ≤ chi ρ r := by
  have hrdiv : 0 ≤ r / ρ := div_nonneg hr hρ.le
  have harg : 2 - 4 * r / ρ ≤ 2 - 2 * r / ρ := by
    simp only [mul_div_assoc]
    linarith
  exact min_le_min_left 1 (max_le_max_left 0 harg)

theorem chi_le_tail {ρ : ℝ} (hρ : 0 < ρ) (r : ℝ) (_hr : 0 ≤ r) (hrρ : r ≤ ρ) :
    chi ρ r ≤ 2 * (ρ - r) / ρ := by
  have hdiv : 2 * r / ρ ≤ 2 := (div_le_iff₀ hρ).2 (by nlinarith)
  have harg : 0 ≤ 2 - 2 * r / ρ := by linarith
  calc
    chi ρ r ≤ 2 - 2 * r / ρ := by
      simp only [chi, max_eq_right harg]
      exact min_le_right _ _
    _ = 2 * (ρ - r) / ρ := by
      field_simp [ne_of_gt hρ]

theorem beta_le_tail {ρ : ℝ} (hρ : 0 < ρ) (r : ℝ) (hr : 0 ≤ r) (hrρ : r ≤ ρ) :
    beta ρ r ≤ 2 * (ρ - r) / ρ :=
  (beta_le_chi hρ r hr).trans (chi_le_tail hρ r hr hrρ)

end ThompsonNonamenability.Analytic

end

end OAI

end
end

section
section
namespace OAI

/-!
# Elementary inputs and explicit formula for the tube correction

Every field below is a scalar, curve, or rotation identity/estimate. In
particular, no property of the corrected map is included in the inputs.
-/

noncomputable section


namespace ThompsonNonamenability.Analytic

open scoped InnerProductSpace

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

structure CorrectionData (C : RegularCurveData E) where
  a : ℝ → ℝ
  v : ℝ → E
  q : ℝ → ℝ
  R : ℝ → E →L[ℝ] E
  curve_eq : ∀ t, C.curve t = a t • v t
  a_zero : a 0 = 0
  a_upper : ∀ t, a t ≤ 5 / 16
  a_late_lower : ∀ t, 1 < t → 1 / 8 ≤ a t
  q_eq : ∀ t, q t = min (a t) (-1 / 8) - a t
  q_bound : ∀ t, |q t| ≤ 7 / 16
  q_lipschitz : ∀ s t, |q t - q s| ≤ (1 / 8) * |t - s|
  norm_v : ∀ t, ‖v t‖ = 1
  v_lipschitz : ∀ s t, ‖v t - v s‖ ≤ |t - s|
  curve_lipschitz : ∀ s t, ‖C.curve t - C.curve s‖ ≤ (7 / 16) * |t - s|
  norm_R : ∀ t e, ‖R t e‖ = ‖e‖
  R_perp : ∀ t e, ⟪e, C.tangent t⟫_ℝ = 0 → ⟪R t e, v t⟫_ℝ = 0
  R_lipschitz : ∀ s t e, ‖R t e - R s e‖ ≤ 238 * |t - s| * ‖e‖
  R_early : ∀ t, t ≤ 1 → ∀ e, R t e = e
  tangent_early : ∀ t, t ≤ 1 → C.tangent t = v t

namespace CorrectionData

variable {C : RegularCurveData E} (D : CorrectionData C)

/-- The additive change on the actual, uniquely parameterized open tube. -/
def change (x : C.tube) : E :=
  (beta C.rho ‖C.residual x‖ * D.q (C.parameter x)) • D.v (C.parameter x) +
    chi C.rho ‖C.residual x‖ • (D.R (C.parameter x) (C.residual x) - C.residual x)

/-- The actual correction inside the tube. -/
def inside (x : C.tube) : E := (x : E) + D.change x

/-- Gluing to the identity outside the open tube, including its boundary. -/
def G (x : E) : E := by
  classical
  exact if hx : x ∈ C.tube then D.inside ⟨x, hx⟩ else x

theorem G_of_mem (x : C.tube) : D.G (x : E) = D.inside x := by
  simp only [G, dif_pos x.property]

theorem G_of_not_mem {x : E} (hx : x ∉ C.tube) : D.G x = x := by
  simp only [G, dif_neg hx]

theorem inside_radial (x : C.tube) :
    D.inside x =
      (D.a (C.parameter x) + beta C.rho ‖C.residual x‖ * D.q (C.parameter x)) •
        D.v (C.parameter x) +
      ((1 - chi C.rho ‖C.residual x‖) • C.residual x +
        chi C.rho ‖C.residual x‖ • D.R (C.parameter x) (C.residual x)) := by
  have hx := C.curve_add_residual x
  rw [D.curve_eq] at hx
  unfold inside change
  rw [← hx]
  simp only [add_smul, sub_smul, one_smul, smul_sub]
  abel

include D in
theorem curve_zero : C.curve 0 = 0 := by
  rw [D.curve_eq, D.a_zero, zero_smul]

theorem norm_curve (t : ℝ) : ‖C.curve t‖ = |D.a t| := by
  rw [D.curve_eq, norm_smul, Real.norm_eq_abs, D.norm_v, mul_one]

theorem q_eq_zero {t : ℝ} (h : D.a t ≤ -1 / 8) : D.q t = 0 := by
  rw [D.q_eq, min_eq_left h, sub_self]

theorem radial_eq_min (t : ℝ) : D.a t + D.q t = min (D.a t) (-1 / 8) := by
  rw [D.q_eq]
  ring

end CorrectionData

end ThompsonNonamenability.Analytic

end

end OAI

end
end

section
section
namespace OAI

/-!
# The local Lipschitz estimate for the explicit tube correction

The radius is the distance to the curve, so its Lipschitz constant is one.
The residual itself has local Lipschitz constant eight. Keeping these two
estimates separate gives the stated constant for the two cutoff terms.
-/

noncomputable section


namespace ThompsonNonamenability.Analytic

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private theorem norm_smul_sub_smul_bound (a b : ℝ) (u v : E) :
    ‖a • u - b • v‖ ≤ |a| * ‖u - v‖ + |a - b| * ‖v‖ := by
  have hid : a • u - b • v = a • (u - v) + (a - b) • v := by
    simp only [smul_sub, sub_smul]
    abel
  rw [hid]
  exact (norm_add_le _ _).trans_eq (by simp only [norm_smul, Real.norm_eq_abs])

namespace RegularCurveData

variable (C : RegularCurveData E)

/-- The residual length is the actual distance to the curve. -/
theorem residual_radius_lipschitz (x y : C.tube) :
    |‖C.residual x‖ - ‖C.residual y‖| ≤ ‖(x : E) - (y : E)‖ := by
  have hxy := Metric.infDist_le_infDist_add_dist
    (x := (x : E)) (y := (y : E)) (s := Set.range C.curve)
  have hyx := Metric.infDist_le_infDist_add_dist
    (x := (y : E)) (y := (x : E)) (s := Set.range C.curve)
  rw [dist_eq_norm] at hxy hyx
  rw [norm_sub_rev (y : E) (x : E)] at hyx
  rw [C.residual_norm, C.residual_norm, abs_le]
  constructor <;> linarith

end RegularCurveData

namespace CorrectionData

variable {C : RegularCurveData E} (D : CorrectionData C)

include D in
/-- Subtracting the nearest curve points costs at most another seven times
the distance, on the local parameter-comparison scale. -/
theorem residual_local_bound (x y : C.tube)
    (hxy : ‖(x : E) - (y : E)‖ < C.rho) :
    ‖C.residual x - C.residual y‖ ≤ 8 * ‖(x : E) - (y : E)‖ := by
  have ht := C.parameter_local_bound16 x y hxy
  have hc := D.curve_lipschitz (C.parameter y) (C.parameter x)
  have hc' : ‖C.curve (C.parameter x) - C.curve (C.parameter y)‖ ≤
      7 * ‖(x : E) - (y : E)‖ := by
    linarith
  have hid : C.residual x - C.residual y =
      ((x : E) - (y : E)) -
        (C.curve (C.parameter x) - C.curve (C.parameter y)) := by
    simp only [RegularCurveData.residual]
    abel
  rw [hid]
  have hn := norm_sub_le ((x : E) - (y : E))
    (C.curve (C.parameter x) - C.curve (C.parameter y))
  linarith

/-- Local Lipschitz control of the actual corrected point. -/
theorem inside_local_bound (x y : C.tube)
    (hxy : ‖(x : E) - (y : E)‖ < C.rho) :
    ‖D.inside x - D.inside y‖ ≤
      (30 + 7 / (4 * C.rho) + 3808 * C.rho) * ‖(x : E) - (y : E)‖ := by
  let d : ℝ := ‖(x : E) - (y : E)‖
  let s : ℝ := C.parameter x
  let t : ℝ := C.parameter y
  let e : E := C.residual x
  let f : E := C.residual y
  have hd : 0 ≤ d := norm_nonneg _
  have hrho : 0 < C.rho := C.rho_pos
  have he : ‖e‖ ≤ C.rho := (C.residual_norm_lt x).le
  have hf : ‖f‖ ≤ C.rho := (C.residual_norm_lt y).le
  have hst : |s - t| ≤ 16 * d := C.parameter_local_bound16 x y hxy
  have hef : ‖e - f‖ ≤ 8 * d := D.residual_local_bound x y hxy
  have hr : |‖e‖ - ‖f‖| ≤ d := C.residual_radius_lipschitz x y
  have hq : |D.q s - D.q t| ≤ 2 * d := by
    have h := D.q_lipschitz t s
    linarith
  have hv : ‖D.v s - D.v t‖ ≤ 16 * d :=
    (D.v_lipschitz t s).trans hst
  have hqv : ‖D.q s • D.v s - D.q t • D.v t‖ ≤ 9 * d := by
    calc
      ‖D.q s • D.v s - D.q t • D.v t‖
          ≤ |D.q s| * ‖D.v s - D.v t‖ +
            |D.q s - D.q t| * ‖D.v t‖ := norm_smul_sub_smul_bound _ _ _ _
      _ ≤ (7 / 16) * (16 * d) + (2 * d) * 1 :=
        add_le_add
          (mul_le_mul (D.q_bound s) hv (norm_nonneg _) (by norm_num))
          (mul_le_mul hq (le_of_eq (D.norm_v t)) (norm_nonneg _) (by positivity))
      _ = 9 * d := by ring
  have hqvt : ‖D.q t • D.v t‖ ≤ 7 / 16 := by
    simpa only [norm_smul, Real.norm_eq_abs, D.norm_v, mul_one] using D.q_bound t
  have hbeta : |beta C.rho ‖e‖ - beta C.rho ‖f‖| ≤ (4 / C.rho) * d :=
    (beta_abs_sub_le hrho _ _).trans
      (mul_le_mul_of_nonneg_left hr (by positivity))
  have hchi : |chi C.rho ‖e‖ - chi C.rho ‖f‖| ≤ (2 / C.rho) * d :=
    (chi_abs_sub_le hrho _ _).trans
      (mul_le_mul_of_nonneg_left hr (by positivity))
  have hbeta_abs : |beta C.rho ‖e‖| ≤ 1 := by
    rw [abs_of_nonneg (beta_nonneg _ _)]
    exact beta_le_one _ _
  have hchi_abs : |chi C.rho ‖e‖| ≤ 1 := by
    rw [abs_of_nonneg (chi_nonneg _ _)]
    exact chi_le_one _ _
  have hradial :
      ‖(beta C.rho ‖e‖ * D.q s) • D.v s -
        (beta C.rho ‖f‖ * D.q t) • D.v t‖ ≤
      (9 + 7 / (4 * C.rho)) * d := by
    rw [mul_smul, mul_smul]
    calc
      ‖beta C.rho ‖e‖ • (D.q s • D.v s) -
          beta C.rho ‖f‖ • (D.q t • D.v t)‖
          ≤ |beta C.rho ‖e‖| * ‖D.q s • D.v s - D.q t • D.v t‖ +
            |beta C.rho ‖e‖ - beta C.rho ‖f‖| * ‖D.q t • D.v t‖ :=
        norm_smul_sub_smul_bound _ _ _ _
      _ ≤ 1 * (9 * d) + ((4 / C.rho) * d) * (7 / 16) :=
        add_le_add
          (mul_le_mul hbeta_abs hqv (norm_nonneg _) zero_le_one)
          (mul_le_mul hbeta hqvt (norm_nonneg _) (by positivity))
      _ = (9 + 7 / (4 * C.rho)) * d := by
        field_simp [ne_of_gt hrho] ; ring
  have hrotation : ‖D.R s f - D.R t f‖ ≤ 3808 * C.rho * d := by
    calc
      ‖D.R s f - D.R t f‖ ≤ 238 * |s - t| * ‖f‖ := D.R_lipschitz t s f
      _ ≤ (238 * (16 * d)) * C.rho :=
        mul_le_mul (mul_le_mul_of_nonneg_left hst (by norm_num)) hf
          (norm_nonneg _) (by positivity)
      _ = 3808 * C.rho * d := by ring
  have hdefect_norm : ‖D.R t f - f‖ ≤ 2 * C.rho := by
    have h := norm_sub_le (D.R t f) f
    rw [D.norm_R] at h
    linarith
  have hdefect : ‖(D.R s e - e) - (D.R t f - f)‖ ≤
      (16 + 3808 * C.rho) * d := by
    have hid : (D.R s e - e) - (D.R t f - f) =
        (D.R s (e - f) + (D.R s f - D.R t f)) - (e - f) := by
      rw [map_sub]
      abel
    calc
      ‖(D.R s e - e) - (D.R t f - f)‖
          = ‖(D.R s (e - f) + (D.R s f - D.R t f)) - (e - f)‖ := by rw [hid]
      _ ≤ ‖D.R s (e - f) + (D.R s f - D.R t f)‖ + ‖e - f‖ := norm_sub_le _ _
      _ ≤ (‖D.R s (e - f)‖ + ‖D.R s f - D.R t f‖) + ‖e - f‖ :=
        add_le_add (norm_add_le _ _) le_rfl
      _ = (‖e - f‖ + ‖D.R s f - D.R t f‖) + ‖e - f‖ := by rw [D.norm_R]
      _ ≤ (8 * d + 3808 * C.rho * d) + 8 * d :=
        add_le_add (add_le_add hef hrotation) hef
      _ = (16 + 3808 * C.rho) * d := by ring
  have hangular :
      ‖chi C.rho ‖e‖ • (D.R s e - e) - chi C.rho ‖f‖ • (D.R t f - f)‖ ≤
        (20 + 3808 * C.rho) * d := by
    calc
      ‖chi C.rho ‖e‖ • (D.R s e - e) - chi C.rho ‖f‖ • (D.R t f - f)‖
          ≤ |chi C.rho ‖e‖| * ‖(D.R s e - e) - (D.R t f - f)‖ +
            |chi C.rho ‖e‖ - chi C.rho ‖f‖| * ‖D.R t f - f‖ :=
        norm_smul_sub_smul_bound _ _ _ _
      _ ≤ 1 * ((16 + 3808 * C.rho) * d) + ((2 / C.rho) * d) * (2 * C.rho) :=
        add_le_add
          (mul_le_mul hchi_abs hdefect (norm_nonneg _) zero_le_one)
          (mul_le_mul hchi hdefect_norm (norm_nonneg _) (by positivity))
      _ = (20 + 3808 * C.rho) * d := by
        field_simp [ne_of_gt hrho] ; ring
  have hchange : ‖D.change x - D.change y‖ ≤
      (29 + 7 / (4 * C.rho) + 3808 * C.rho) * d := by
    have hid : D.change x - D.change y =
        ((beta C.rho ‖e‖ * D.q s) • D.v s -
          (beta C.rho ‖f‖ * D.q t) • D.v t) +
        (chi C.rho ‖e‖ • (D.R s e - e) -
          chi C.rho ‖f‖ • (D.R t f - f)) := by
      dsimp [change, s, t, e, f]
      abel
    rw [hid]
    exact (norm_add_le _ _).trans ((add_le_add hradial hangular).trans_eq (by ring))
  have hid : D.inside x - D.inside y =
      ((x : E) - (y : E)) + (D.change x - D.change y) := by
    simp only [inside]
    abel
  rw [hid]
  calc
    ‖((x : E) - (y : E)) + (D.change x - D.change y)‖
        ≤ d + ‖D.change x - D.change y‖ := norm_add_le _ _
    _ ≤ d + (29 + 7 / (4 * C.rho) + 3808 * C.rho) * d := add_le_add le_rfl hchange
    _ = (30 + 7 / (4 * C.rho) + 3808 * C.rho) * ‖(x : E) - (y : E)‖ := by
      change d + (29 + 7 / (4 * C.rho) + 3808 * C.rho) * d =
        (30 + 7 / (4 * C.rho) + 3808 * C.rho) * d
      ring

end CorrectionData

end ThompsonNonamenability.Analytic

end

end OAI

end
end

section
section
namespace OAI

/-!
# The correction stays away from zero and fixes the outer annulus

The lower bound follows from the two orthogonal inner regions and the two
parameter cases in the outer tube region. All estimates concern the explicit
formula defined in `CorrectionData`.
-/

noncomputable section


namespace ThompsonNonamenability.Analytic

open Set
open scoped InnerProductSpace

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

namespace CorrectionData

variable {C : RegularCurveData E} (D : CorrectionData C)

private theorem norm_left_le_of_perp {u w : E} (h : ⟪u, w⟫_ℝ = 0) :
    ‖u‖ ≤ ‖u + w‖ := by
  have heq := norm_add_sq_eq_norm_sq_add_norm_sq_real h
  nlinarith [norm_nonneg u, norm_nonneg (u + w), sq_nonneg ‖w‖]

private theorem norm_right_le_of_perp {u w : E} (h : ⟪u, w⟫_ℝ = 0) :
    ‖w‖ ≤ ‖u + w‖ := by
  have heq := norm_add_sq_eq_norm_sq_add_norm_sq_real h
  nlinarith [norm_nonneg w, norm_nonneg (u + w), sq_nonneg ‖u‖]

private theorem radial_perp (a : ℝ) {v w : E} (h : ⟪w, v⟫_ℝ = 0) :
    ⟪a • v, w⟫_ℝ = 0 := by
  have hvw : ⟪v, w⟫_ℝ = 0 := by rw [real_inner_comm]; exact h
  simp only [real_inner_smul_left, hvw, mul_zero]

/-- The orthogonal formula throughout the inner half of the tube. -/
theorem inside_inner_formula (x : C.tube) (hr : ‖C.residual x‖ ≤ C.rho / 2) :
    D.inside x =
      (D.a (C.parameter x) + beta C.rho ‖C.residual x‖ * D.q (C.parameter x)) •
        D.v (C.parameter x) + D.R (C.parameter x) (C.residual x) := by
  rw [D.inside_radial, chi_eq_one C.rho_pos _ hr]
  simp only [sub_self, zero_smul, one_smul, zero_add]

private theorem inside_inner_radial_lower (x : C.tube)
    (hr : ‖C.residual x‖ ≤ C.rho / 2) :
    |D.a (C.parameter x) + beta C.rho ‖C.residual x‖ * D.q (C.parameter x)| ≤
      ‖D.inside x‖ := by
  rw [D.inside_inner_formula x hr]
  have h := norm_left_le_of_perp
    (radial_perp
      (D.a (C.parameter x) + beta C.rho ‖C.residual x‖ * D.q (C.parameter x))
      (D.R_perp _ _ (C.residual_perp_u x)))
  simpa only [norm_smul, Real.norm_eq_abs, D.norm_v, mul_one] using h

private theorem inside_inner_residual_lower (x : C.tube)
    (hr : ‖C.residual x‖ ≤ C.rho / 2) :
    ‖C.residual x‖ ≤ ‖D.inside x‖ := by
  rw [D.inside_inner_formula x hr]
  have h := norm_right_le_of_perp
    (radial_perp
      (D.a (C.parameter x) + beta C.rho ‖C.residual x‖ * D.q (C.parameter x))
      (D.R_perp _ _ (C.residual_perp_u x)))
  simpa only [D.norm_R] using h

/-- Convex interpolation between the identity and the rotation is a contraction
on each individual residual. -/
theorem residual_blend_norm_le (x : C.tube) :
    ‖(1 - chi C.rho ‖C.residual x‖) • C.residual x +
      chi C.rho ‖C.residual x‖ • D.R (C.parameter x) (C.residual x)‖ ≤
      ‖C.residual x‖ := by
  have hχ := chi_nonneg C.rho ‖C.residual x‖
  have hχ' := chi_le_one C.rho ‖C.residual x‖
  calc
    _ ≤ ‖(1 - chi C.rho ‖C.residual x‖) • C.residual x‖ +
        ‖chi C.rho ‖C.residual x‖ • D.R (C.parameter x) (C.residual x)‖ :=
      norm_add_le _ _
    _ = (1 - chi C.rho ‖C.residual x‖) * ‖C.residual x‖ +
        chi C.rho ‖C.residual x‖ * ‖C.residual x‖ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (sub_nonneg.mpr hχ'), abs_of_nonneg hχ, D.norm_R]
    _ = ‖C.residual x‖ := by ring

/-- On the early part of the curve the rotation term vanishes identically. -/
theorem inside_early_formula (x : C.tube) (ht : C.parameter x ≤ 1) :
    D.inside x =
      (D.a (C.parameter x) + beta C.rho ‖C.residual x‖ * D.q (C.parameter x)) •
        D.v (C.parameter x) + C.residual x := by
  rw [D.inside_radial, D.R_early _ ht]
  congr 1
  rw [← add_smul]
  have heq : 1 - chi C.rho ‖C.residual x‖ + chi C.rho ‖C.residual x‖ = 1 :=
    sub_add_cancel _ _
  rw [heq, one_smul]

private theorem inside_early_residual_lower (x : C.tube)
    (ht : C.parameter x ≤ 1) : ‖C.residual x‖ ≤ ‖D.inside x‖ := by
  rw [D.inside_early_formula x ht]
  have hperp : ⟪C.residual x, D.v (C.parameter x)⟫_ℝ = 0 := by
    have h := C.residual_perp_u x
    rwa [D.tangent_early _ ht] at h
  exact norm_right_le_of_perp (radial_perp _ hperp)

/-- The four tube regions give the same positive lower bound. -/
theorem inside_lower (x : C.tube) : C.rho / 4 ≤ ‖D.inside x‖ := by
  have hρ := C.rho_le
  have hρpos := C.rho_pos
  by_cases hquarter : ‖C.residual x‖ ≤ C.rho / 4
  · have hhalf : ‖C.residual x‖ ≤ C.rho / 2 := by linarith
    have h := D.inside_inner_radial_lower x hhalf
    rw [beta_eq_one C.rho_pos _ hquarter, one_mul, D.radial_eq_min] at h
    have hm : min (D.a (C.parameter x)) (-1 / 8) ≤ -1 / 8 := min_le_right _ _
    rw [abs_of_nonpos (by linarith : min (D.a (C.parameter x)) (-1 / 8) ≤ 0)] at h
    linarith
  · have hquarter' : C.rho / 4 ≤ ‖C.residual x‖ := le_of_not_ge hquarter
    by_cases hhalf : ‖C.residual x‖ ≤ C.rho / 2
    · exact hquarter'.trans (D.inside_inner_residual_lower x hhalf)
    · have hhalf' : C.rho / 2 ≤ ‖C.residual x‖ := le_of_not_ge hhalf
      by_cases ht : C.parameter x ≤ 1
      · exact hquarter'.trans (D.inside_early_residual_lower x ht)
      · have ha : 1 / 8 ≤ D.a (C.parameter x) :=
          D.a_late_lower _ (lt_of_not_ge ht)
        have hrad := D.inside_radial x
        rw [beta_eq_zero C.rho_pos _ hhalf', zero_mul, add_zero] at hrad
        let w : E := (1 - chi C.rho ‖C.residual x‖) • C.residual x +
          chi C.rho ‖C.residual x‖ • D.R (C.parameter x) (C.residual x)
        have hw : ‖w‖ ≤ ‖C.residual x‖ := D.residual_blend_norm_le x
        have htriangle : ‖D.a (C.parameter x) • D.v (C.parameter x)‖ ≤
            ‖D.inside x‖ + ‖w‖ := by
          rw [hrad]
          simpa only [add_sub_cancel_right] using
            norm_sub_le (D.a (C.parameter x) • D.v (C.parameter x) + w) w
        rw [norm_smul, Real.norm_eq_abs, D.norm_v, mul_one,
          abs_of_nonneg (by linarith : 0 ≤ D.a (C.parameter x))] at htriangle
        have hr := C.residual_norm_lt x
        linarith

/-- The explicit correction has a uniform positive norm everywhere. -/
theorem G_lower (x : E) : C.rho / 4 ≤ ‖D.G x‖ := by
  by_cases hx : x ∈ C.tube
  · rw [D.G_of_mem ⟨x, hx⟩]
    exact D.inside_lower ⟨x, hx⟩
  · rw [D.G_of_not_mem hx]
    have hdist : C.rho ≤ Metric.infDist x (range C.curve) := by
      exact le_of_not_gt hx
    have hzero : (0 : E) ∈ range C.curve := ⟨0, D.curve_zero⟩
    have hnorm : Metric.infDist x (range C.curve) ≤ ‖x‖ := by
      simpa only [dist_zero_right] using Metric.infDist_le_dist_of_mem hzero
    have hρ := C.rho_pos
    linarith

/-- Any tube point of norm at least one half has parameter on the unchanged
negative ray, so both additive corrections vanish. -/
theorem inside_outer (x : C.tube) (hx : 1 / 2 ≤ ‖(x : E)‖) :
    D.inside x = (x : E) := by
  have htriangle : ‖(x : E)‖ ≤ |D.a (C.parameter x)| + ‖C.residual x‖ := by
    calc
      ‖(x : E)‖ = ‖C.curve (C.parameter x) + C.residual x‖ :=
        congrArg norm (C.curve_add_residual x).symm
      _ ≤ ‖C.curve (C.parameter x)‖ + ‖C.residual x‖ := norm_add_le _ _
      _ = |D.a (C.parameter x)| + ‖C.residual x‖ := by rw [D.norm_curve]
  have hr := C.residual_norm_lt x
  have hρ := C.rho_le
  have haupper := D.a_upper (C.parameter x)
  have haneg : D.a (C.parameter x) < -1 / 8 := by
    by_contra hn
    have ha_lower : -1 / 8 ≤ D.a (C.parameter x) := le_of_not_gt hn
    have habs : |D.a (C.parameter x)| ≤ 5 / 16 :=
      abs_le.mpr ⟨by linarith, haupper⟩
    linarith
  have ht : C.parameter x ≤ 1 := by
    by_contra hn
    have := D.a_late_lower (C.parameter x) (lt_of_not_ge hn)
    linarith
  have hq : D.q (C.parameter x) = 0 := D.q_eq_zero haneg.le
  unfold inside change
  rw [hq, mul_zero, zero_smul, D.R_early _ ht, sub_self, smul_zero,
    add_zero, add_zero]

/-- The correction is exactly the identity on the whole outer annulus. -/
theorem G_outer (x : E) (hx : 1 / 2 ≤ ‖x‖) : D.G x = x := by
  by_cases htube : x ∈ C.tube
  · rw [D.G_of_mem ⟨x, htube⟩]
    exact D.inside_outer ⟨x, htube⟩ hx
  · exact D.G_of_not_mem htube

end CorrectionData

end ThompsonNonamenability.Analytic

end

end OAI

end
end

section
section
namespace OAI

/-!
# Global gluing of the explicit Hilbert correction

The cutoff tails tend to zero at the actual tube boundary. These estimates
give the mixed inside/outside case; a uniform bound on the additive change
handles distant pairs. Together with the local tube estimate, this covers
every pair of points, including the boundary itself.
-/

noncomputable section


namespace ThompsonNonamenability.Analytic

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {C : RegularCurveData E}

namespace CorrectionData

variable (D : CorrectionData C)

theorem rotated_residual_sub_bound (x : C.tube) :
    ‖D.R (C.parameter x) (C.residual x) - C.residual x‖ ≤ 2 * ‖C.residual x‖ := by
  calc
    _ ≤ ‖D.R (C.parameter x) (C.residual x)‖ + ‖C.residual x‖ := norm_sub_le _ _
    _ = _ := by rw [D.norm_R]; ring

theorem change_bound (x : C.tube) :
    ‖D.change x‖ ≤ beta C.rho ‖C.residual x‖ * (7 / 16) +
      chi C.rho ‖C.residual x‖ * (2 * ‖C.residual x‖) := by
  calc
    _ ≤ ‖(beta C.rho ‖C.residual x‖ * D.q (C.parameter x)) • D.v (C.parameter x)‖ +
        ‖chi C.rho ‖C.residual x‖ •
          (D.R (C.parameter x) (C.residual x) - C.residual x)‖ := norm_add_le _ _
    _ = beta C.rho ‖C.residual x‖ * |D.q (C.parameter x)| +
        chi C.rho ‖C.residual x‖ *
          ‖D.R (C.parameter x) (C.residual x) - C.residual x‖ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_mul, abs_of_nonneg (beta_nonneg _ _),
        abs_of_nonneg (chi_nonneg _ _), D.norm_v, mul_one]
    _ ≤ _ := add_le_add
      (mul_le_mul_of_nonneg_left (D.q_bound _) (beta_nonneg _ _))
      (mul_le_mul_of_nonneg_left (D.rotated_residual_sub_bound x) (chi_nonneg _ _))

theorem change_uniform_bound (x : C.tube) :
    ‖D.change x‖ ≤ 7 / 16 + 2 * C.rho := by
  have hb := beta_le_one C.rho ‖C.residual x‖
  have hc := chi_le_one C.rho ‖C.residual x‖
  have hr := (C.residual_norm_lt x).le
  have hchi := mul_le_mul_of_nonneg_right hc
    (show 0 ≤ 2 * ‖C.residual x‖ by positivity)
  have hbeta := mul_le_mul_of_nonneg_right hb (show (0 : ℝ) ≤ 7 / 16 by norm_num)
  have h := D.change_bound x
  linarith

theorem change_tail_bound (x : C.tube) :
    ‖D.change x‖ ≤ (7 / (8 * C.rho) + 4) * (C.rho - ‖C.residual x‖) := by
  have hr := (C.residual_norm_lt x).le
  have ht : 0 ≤ 2 * (C.rho - ‖C.residual x‖) / C.rho :=
    div_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr hr)) C.rho_pos.le
  have hb := beta_le_tail C.rho_pos ‖C.residual x‖ (norm_nonneg _) hr
  have hc := chi_le_tail C.rho_pos ‖C.residual x‖ (norm_nonneg _) hr
  calc
    ‖D.change x‖ ≤ beta C.rho ‖C.residual x‖ * (7 / 16) +
        chi C.rho ‖C.residual x‖ * (2 * ‖C.residual x‖) := D.change_bound x
    _ ≤ (2 * (C.rho - ‖C.residual x‖) / C.rho) * (7 / 16) +
        (2 * (C.rho - ‖C.residual x‖) / C.rho) * (2 * C.rho) := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_right hb (by norm_num)
      · exact (mul_le_mul_of_nonneg_right hc (by positivity)).trans
          (mul_le_mul_of_nonneg_left (by linarith : 2 * ‖C.residual x‖ ≤ 2 * C.rho) ht)
    _ = _ := by field_simp [C.rho_pos.ne']; ring

/-- Distance to an outside point controls the remaining radius of the tube. -/
theorem radius_gap_le (x : C.tube) {y : E} (hy : y ∉ C.tube) :
    C.rho - ‖C.residual x‖ ≤ ‖(x : E) - y‖ := by
  have hy' : C.rho ≤ Metric.infDist y (Set.range C.curve) := by
    exact not_lt.mp hy
  have hdist : Metric.infDist y (Set.range C.curve) ≤
      Metric.infDist (x : E) (Set.range C.curve) + ‖(x : E) - y‖ := by
    simpa only [dist_eq_norm, norm_sub_rev] using
      (Metric.infDist_le_infDist_add_dist (x := y) (y := (x : E))
        (s := Set.range C.curve))
  rw [← C.residual_norm] at hdist
  linarith

theorem inside_outside_bound (x : C.tube) {y : E} (hy : y ∉ C.tube) :
    ‖D.inside x - y‖ ≤ (5 + 7 / (8 * C.rho)) * ‖(x : E) - y‖ := by
  have hρ := C.rho_pos
  have hc : 0 ≤ 7 / (8 * C.rho) + 4 := by positivity
  have heq : D.inside x - y = ((x : E) - y) + D.change x := by
    unfold inside
    abel
  calc
    ‖D.inside x - y‖ ≤ ‖(x : E) - y‖ + ‖D.change x‖ := by
      rw [heq]
      exact norm_add_le _ _
    _ ≤ ‖(x : E) - y‖ +
        (7 / (8 * C.rho) + 4) * (C.rho - ‖C.residual x‖) :=
      add_le_add le_rfl (D.change_tail_bound x)
    _ ≤ ‖(x : E) - y‖ + (7 / (8 * C.rho) + 4) * ‖(x : E) - y‖ :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left (radius_gap_le (C := C) x hy) hc)
    _ = _ := by ring

theorem G_sub_self_bound (x : E) : ‖D.G x - x‖ ≤ 7 / 16 + 2 * C.rho := by
  by_cases hx : x ∈ C.tube
  · rw [D.G_of_mem ⟨x, hx⟩]
    simpa only [inside, add_sub_cancel_left] using D.change_uniform_bound ⟨x, hx⟩
  · rw [D.G_of_not_mem hx, sub_self, norm_zero]
    have := C.rho_pos
    positivity

/-- The distant-pair estimate uses only the bounded additive change. -/
theorem G_distant_bound (x y : E) (hxy : C.rho ≤ ‖x - y‖) :
    ‖D.G x - D.G y‖ ≤ (5 + 7 / (8 * C.rho)) * ‖x - y‖ := by
  have hρ := C.rho_pos
  have hc : 0 ≤ 7 / (8 * C.rho) + 4 := by positivity
  have hm := mul_le_mul_of_nonneg_left hxy hc
  have he : (7 / (8 * C.rho) + 4) * C.rho = 7 / 8 + 4 * C.rho := by
    field_simp [C.rho_pos.ne']
  rw [he] at hm
  have hdecomp : D.G x - D.G y = (x - y) + ((D.G x - x) - (D.G y - y)) := by abel
  calc
    ‖D.G x - D.G y‖ ≤ ‖x - y‖ + (‖D.G x - x‖ + ‖D.G y - y‖) := by
      rw [hdecomp]
      exact (norm_add_le _ _).trans (add_le_add le_rfl (norm_sub_le _ _))
    _ ≤ ‖x - y‖ + ((7 / 16 + 2 * C.rho) + (7 / 16 + 2 * C.rho)) :=
      add_le_add le_rfl (add_le_add (D.G_sub_self_bound x) (D.G_sub_self_bound y))
    _ ≤ (5 + 7 / (8 * C.rho)) * ‖x - y‖ := by nlinarith

/-- A finite positive constant valid for all pairs in the ambient Hilbert space. -/
def lipschitzConstant (_ : CorrectionData C) : ℝ :=
  max 1 (max (30 + 7 / (4 * C.rho) + 3808 * C.rho) (5 + 7 / (8 * C.rho)))

theorem lipschitzConstant_pos : 0 < D.lipschitzConstant :=
  lt_of_lt_of_le (by norm_num) (le_max_left _ _)

theorem G_lipschitz (x y : E) :
    ‖D.G x - D.G y‖ ≤ D.lipschitzConstant * ‖x - y‖ := by
  have hlocal : 30 + 7 / (4 * C.rho) + 3808 * C.rho ≤ D.lipschitzConstant :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hfar : 5 + 7 / (8 * C.rho) ≤ D.lipschitzConstant :=
    (le_max_right _ _).trans (le_max_right _ _)
  have hone : 1 ≤ D.lipschitzConstant := le_max_left _ _
  by_cases hxy : ‖x - y‖ < C.rho
  · by_cases hx : x ∈ C.tube
    · by_cases hy : y ∈ C.tube
      · rw [D.G_of_mem ⟨x, hx⟩, D.G_of_mem ⟨y, hy⟩]
        exact (D.inside_local_bound ⟨x, hx⟩ ⟨y, hy⟩ hxy).trans
          (mul_le_mul_of_nonneg_right hlocal (norm_nonneg _))
      · rw [D.G_of_mem ⟨x, hx⟩, D.G_of_not_mem hy]
        exact (D.inside_outside_bound ⟨x, hx⟩ hy).trans
          (mul_le_mul_of_nonneg_right hfar (norm_nonneg _))
    · by_cases hy : y ∈ C.tube
      · rw [D.G_of_not_mem hx, D.G_of_mem ⟨y, hy⟩, norm_sub_rev]
        have h := D.inside_outside_bound ⟨y, hy⟩ hx
        rw [norm_sub_rev y x] at h
        exact h.trans (mul_le_mul_of_nonneg_right hfar (norm_nonneg _))
      · rw [D.G_of_not_mem hx, D.G_of_not_mem hy]
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hone (norm_nonneg (x - y))
  · exact (D.G_distant_bound x y (not_lt.mp hxy)).trans
      (mul_le_mul_of_nonneg_right hfar (norm_nonneg _))

end CorrectionData

end ThompsonNonamenability.Analytic

end

end OAI

end
end

section
section
namespace OAI

/-!
# The actual positive-displacement map on the L² unit ball

Every elementary field of the generic tube and correction constructions is
instantiated here by the explicit scalar profiles and the concrete L² curve.
The final map has no geometric or analytic certificate as a hypothesis.
-/

noncomputable section

namespace ThompsonNonamenability.Analytic

open scoped InnerProductSpace

private def separationAtScale : ℝ :=
  Classical.choose (gamma_uniform_separation (1 / 32) (by norm_num))

private theorem separationAtScale_pos : 0 < separationAtScale :=
  (Classical.choose_spec (gamma_uniform_separation (1 / 32) (by norm_num))).1

private theorem separationAtScale_le (s t : ℝ) (h : (1 / 32 : ℝ) ≤ |t - s|) :
    separationAtScale ≤ ‖gamma t - gamma s‖ :=
  (Classical.choose_spec (gamma_uniform_separation (1 / 32) (by norm_num))).2 s t h

/-- The proved elementary geometry of the actual radial oscillating curve. -/
def regularCurve : RegularCurveData Hilbert where
  curve := gamma
  velocity := gammaDeriv
  tangent := u
  hasDerivAt := hasDerivAt_gamma
  norm_tangent := u_norm
  velocity_eq := gammaDeriv_eq_norm_smul_u
  speed_lower := gammaDeriv_speed_lower
  velocity_lipschitz := gammaDeriv_sub_norm_le
  tangent_lipschitz := u_sub_norm_le
  separation := separationAtScale
  separation_pos := separationAtScale_pos
  separated := separationAtScale_le

/-- The radius comes from proved uniform separation and the explicit speed bounds. -/
def tubeRadius : ℝ := regularCurve.rho

theorem tubeRadius_pos : 0 < tubeRadius := regularCurve.rho_pos

/-- The literal radial, angular, and rotation inputs to the correction formula. -/
def correctionData : CorrectionData regularCurve where
  a := a
  v := v
  q := q
  R := R
  curve_eq := fun _ => rfl
  a_zero := by rw [a_of_le_two (by norm_num : (0 : ℝ) ≤ 2)]; norm_num
  a_upper := a_le_five_sixteenths
  a_late_lower := fun _ ht => a_lower_of_one_le ht.le
  q_eq := fun t => by simpa only [b, neg_div] using q_eq_b_sub_a t
  q_bound := q_abs_le
  q_lipschitz := by
    intro s t
    simpa [dist_eq_norm, Real.norm_eq_abs] using q_lipschitz.dist_le_mul t s
  norm_v := v_norm
  v_lipschitz := v_sub_norm_le
  curve_lipschitz := gamma_sub_norm_le
  norm_R := R_norm
  R_perp := R_perp
  R_lipschitz := R_sub_norm_le
  R_early := fun _ ht e => R_early_apply ht e
  tangent_early := fun _ ht => u_of_le_one ht

/-- The explicit correction, restricted to the shared actual closed unit ball. -/
def G (x : Ball) : Hilbert := correctionData.G (x : Hilbert)

theorem G_norm_lower (x : Ball) : tubeRadius / 4 ≤ ‖G x‖ :=
  correctionData.G_lower (x : Hilbert)

theorem G_outer (x : Ball) (hx : (1 / 2 : ℝ) ≤ ‖(x : Hilbert)‖) :
    G x = (x : Hilbert) := correctionData.G_outer (x : Hilbert) hx

theorem G_sub_norm_le (x y : Ball) :
    ‖G x - G y‖ ≤ correctionData.lipschitzConstant * ‖(x : Hilbert) - y‖ :=
  correctionData.G_lipschitz (x : Hilbert) (y : Hilbert)

private theorem normalizationRadius_pos : 0 < tubeRadius / 4 :=
  div_pos tubeRadius_pos (by norm_num)

/-- Negative radial normalization of the concrete nonvanishing correction. -/
def displacementMap : Ball → Ball :=
  normalizedMap G normalizationRadius_pos G_norm_lower

theorem displacementMap_displacement (x : Ball) :
    (1 / 2 : ℝ) ≤ ‖(displacementMap x : Hilbert) - x‖ :=
  normalizedMap_displacement G normalizationRadius_pos G_norm_lower G_outer x

def displacementLipschitzConstant : ℝ :=
  2 * correctionData.lipschitzConstant / (tubeRadius / 4)

theorem displacementLipschitzConstant_pos : 0 < displacementLipschitzConstant :=
  div_pos (mul_pos (by norm_num) correctionData.lipschitzConstant_pos)
    normalizationRadius_pos

theorem displacementMap_lipschitz (x y : Ball) :
    ‖(displacementMap x : Hilbert) - displacementMap y‖ ≤
      displacementLipschitzConstant * ‖(x : Hilbert) - y‖ :=
  normalizedMap_lipschitz G normalizationRadius_pos G_norm_lower G_sub_norm_le x y

end ThompsonNonamenability.Analytic

end

end OAI

end
end

section
section
namespace OAI

/-!
# Positive normalized left-invariant means

The domain is the actual space of all bounded real functions on the group.
Continuity is a consequence of positivity and normalization, not an assumption.
-/

noncomputable section

open scoped ENNReal


namespace ThompsonNonamenability

@[simp]
theorem BoundedReal.smul_one_apply {G : Type uG} (r : ℝ) (g : G) :
    (r • (1 : BoundedReal G)) g = r := by
  simp [lp.coeFn_smul, lp.infty_coeFn_one]

variable {G : Type uG} [Group G]

@[simp]
theorem leftPull_apply (h : G) (f : BoundedReal G) (g : G) :
    leftPull h f g = f (h * g) := rfl

@[simp]
theorem leftPull_one (f : BoundedReal G) : leftPull (1 : G) f = f := by
  apply lp.ext
  funext g
  simp

namespace InvariantMean

instance : CoeFun (InvariantMean G) (fun _ => BoundedReal G → ℝ) :=
  ⟨fun M => M.toLinearMap⟩

@[simp]
theorem map_zero (M : InvariantMean G) : M 0 = 0 := M.toLinearMap.map_zero

@[simp]
theorem map_add (M : InvariantMean G) (f g : BoundedReal G) :
    M (f + g) = M f + M g := M.toLinearMap.map_add f g

@[simp]
theorem map_sub (M : InvariantMean G) (f g : BoundedReal G) :
    M (f - g) = M f - M g := M.toLinearMap.map_sub f g

@[simp]
theorem map_smul (M : InvariantMean G) (r : ℝ) (f : BoundedReal G) :
    M (r • f) = r * M f := by
  simpa only [smul_eq_mul] using M.toLinearMap.map_smul r f

/-- Evaluation of a constant function. -/
@[simp]
theorem map_const (M : InvariantMean G) (r : ℝ) :
    M (r • (1 : BoundedReal G)) = r := by
  rw [map_smul, M.normalized, mul_one]

/-- Positivity gives monotonicity for the pointwise order. -/
theorem mono (M : InvariantMean G) {f g : BoundedReal G}
    (hfg : ∀ x, f x ≤ g x) : M f ≤ M g := by
  have h := M.positive (g - f) (fun x => sub_nonneg.mpr (hfg x))
  rw [map_sub] at h
  exact sub_nonneg.mp h

/-- A mean has norm at most one, as a consequence of its defining axioms. -/
theorem abs_apply_le_norm (M : InvariantMean G) (f : BoundedReal G) :
    |M f| ≤ ‖f‖ := by
  have hbound (g : G) : -‖f‖ ≤ f g ∧ f g ≤ ‖f‖ := by
    apply abs_le.mp
    simpa only [Real.norm_eq_abs] using
      lp.norm_apply_le_norm ENNReal.top_ne_zero f g
  have hlo := M.mono (f := (-‖f‖) • (1 : BoundedReal G)) (g := f)
    (fun g => by simpa only [BoundedReal.smul_one_apply] using (hbound g).1)
  have hhi := M.mono (f := f) (g := ‖f‖ • (1 : BoundedReal G))
    (fun g => by simpa only [BoundedReal.smul_one_apply] using (hbound g).2)
  rw [map_const] at hlo hhi
  exact abs_le.mpr ⟨hlo, hhi⟩

/-- The continuous functional furnished automatically by a positive normalized mean. -/
def toContinuousLinearMap (M : InvariantMean G) : BoundedReal G →L[ℝ] ℝ :=
  M.toLinearMap.mkContinuous 1 (fun f => by
    simpa only [one_mul, Real.norm_eq_abs] using M.abs_apply_le_norm f)

@[simp]
theorem toContinuousLinearMap_apply (M : InvariantMean G) (f : BoundedReal G) :
    M.toContinuousLinearMap f = M f := rfl

end InvariantMean

end ThompsonNonamenability

end

end OAI

end
end

section
section
namespace OAI

/-!
# Finite probabilities and their simultaneous translation defects

One ℓ¹ space on `S × G` carries the sum of all translation defects.  In
particular its norm is the exact finite sum, without a factor depending on
`S.card`.  This is the finite-probability input to the separation argument.
-/

noncomputable section

open scoped BigOperators Classical


namespace ThompsonNonamenability

variable {G : Type uG}

/-- The total mass of a finitely supported real function. -/
def mass : (G →₀ ℝ) →ₗ[ℝ] ℝ :=
  Finsupp.linearCombination ℝ (fun _ : G => (1 : ℝ))

@[simp]
theorem mass_apply (p : G →₀ ℝ) : mass p = ∑ g ∈ p.support, p g := by
  simp [mass, Finsupp.linearCombination_apply, Finsupp.sum]

@[simp]
theorem mass_single (g : G) (a : ℝ) : mass (Finsupp.single g a) = a := by
  simp [mass]

/-- Nonnegative finite weights with total mass one. -/
def IsProbabilityWeights (p : G →₀ ℝ) : Prop :=
  (∀ g, 0 ≤ p g) ∧ mass p = 1

theorem isProbabilityWeights_single (g : G) :
    IsProbabilityWeights (Finsupp.single g (1 : ℝ)) := by
  refine ⟨?_, mass_single g 1⟩
  intro x
  simp only [Finsupp.single_apply]
  split_ifs
  · exact zero_le_one
  · exact le_rfl

theorem convex_probabilityWeights :
    Convex ℝ {p : G →₀ ℝ | IsProbabilityWeights p} := by
  intro p hp q hq a b ha hb hab
  refine ⟨?_, ?_⟩
  · intro g
    change 0 ≤ a * p g + b * q g
    exact add_nonneg (mul_nonneg ha (hp.1 g)) (mul_nonneg hb (hq.1 g))
  · rw [map_add, map_smul, map_smul, hp.2, hq.2]
    simpa using hab

/-- The simultaneous defects use the ℓ¹ norm on the product index set. -/
abbrev DefectSpace (S : Finset G) := lp (fun _ : ({h // h ∈ S} × G) => ℝ) 1

variable [Group G]

/-- Translation defect of the point probability at `g`. -/
def diracDefect (S : Finset G) (g : G) : DefectSpace S :=
  ∑ h : S, (lp.single 1 (h, h.val * g) (1 : ℝ) - lp.single 1 (h, g) (1 : ℝ))

/-- The linear extension of the point-probability defects. -/
def defectMap (S : Finset G) : (G →₀ ℝ) →ₗ[ℝ] DefectSpace S :=
  Finsupp.linearCombination ℝ (diracDefect S)

@[simp]
theorem defectMap_single (S : Finset G) (g : G) (a : ℝ) :
    defectMap S (Finsupp.single g a) = a • diracDefect S g := by
  simp [defectMap]

private theorem single_apply_real {ι : Type uι} [DecidableEq ι] (i j : ι) (a : ℝ) :
    (lp.single 1 i a : lp (fun _ : ι => ℝ) 1) j = if i = j then a else 0 := by
  by_cases hij : i = j
  · subst j
    simp
  · rw [lp.single_apply_ne (E := fun _ : ι => ℝ) 1 i a (Ne.symm hij), if_neg hij]

/-- Coordinate computation for a single point probability. -/
theorem diracDefect_apply (S : Finset G) (g : G) (h : S) (x : G) :
    diracDefect S g (h, x) =
      (Finsupp.single g (1 : ℝ)) (h.val⁻¹ * x) - (Finsupp.single g (1 : ℝ)) x := by
  have hmul : h.val * g = x ↔ g = h.val⁻¹ * x := by
    constructor
    · intro heq
      simpa [mul_assoc] using congrArg (fun y => h.val⁻¹ * y) heq
    · intro heq
      simpa [mul_assoc] using congrArg (fun y => h.val * y) heq
  unfold diracDefect
  rw [lp.coeFn_sum, Finset.sum_apply, Finset.sum_eq_single h]
  · simp only [lp.coeFn_sub, Pi.sub_apply]
    rw [single_apply_real, single_apply_real]
    simp only [Prod.mk.injEq, true_and, hmul,
      Finsupp.single_apply]
  · intro k _ hkh
    simp [Prod.mk.injEq, hkh]
  · simp

/-- The product coordinate is exactly the left translation difference. -/
theorem defectMap_apply (S : Finset G) (p : G →₀ ℝ) (h : S) (x : G) :
    defectMap S p (h, x) = p (h.val⁻¹ * x) - p x := by
  induction p using Finsupp.induction_linear with
  | zero => simp
  | add p q hp hq =>
      simp only [map_add, lp.coeFn_add, Pi.add_apply, Finsupp.add_apply, hp, hq]
      ring
  | single g a =>
      rw [defectMap_single, lp.coeFn_smul, Pi.smul_apply, diracDefect_apply]
      simp only [smul_eq_mul, Finsupp.single_apply, mul_sub, mul_ite, mul_one, mul_zero]

/-- Each translation difference vanishes outside its exact finite support bound. -/
theorem translation_difference_eq_zero_of_not_mem (p : G →₀ ℝ) (h x : G)
    (hx : x ∉ p.support ∪ p.support.image (fun g => h * g)) :
    p (h⁻¹ * x) - p x = 0 := by
  have hx₀ : x ∉ p.support := fun hmem => hx (Finset.mem_union_left _ hmem)
  have hx₁ : h⁻¹ * x ∉ p.support := by
    intro hmem
    apply hx
    apply Finset.mem_union_right
    exact Finset.mem_image.mpr ⟨h⁻¹ * x, hmem, by simp⟩
  simp [Finsupp.notMem_support_iff.mp hx₀, Finsupp.notMem_support_iff.mp hx₁]

/-- Exact ℓ¹ norm of the simultaneous defect, with no `S.card` loss. -/
theorem norm_defectMap (S : Finset G) (p : G →₀ ℝ) :
    ‖defectMap S p‖ =
      ∑ h ∈ S, ∑ x ∈ p.support ∪ p.support.image (fun g => h * g),
        |p (h⁻¹ * x) - p x| := by
  have hsum : HasSum (fun z : S × G => ‖defectMap S p z‖) ‖defectMap S p‖ := by
    simpa only [ENNReal.toReal_one, Real.rpow_one] using
      (lp.hasSum_norm (p := 1) (by simp) (defectMap S p))
  calc
    ‖defectMap S p‖ = ∑' z : S × G, ‖defectMap S p z‖ := hsum.tsum_eq.symm
    _ = ∑ h : S, ∑' x : G, ‖defectMap S p (h, x)‖ := by
      rw [hsum.summable.tsum_prod, tsum_fintype]
    _ = ∑ h : S, ∑ x ∈ p.support ∪ p.support.image (fun g => h.val * g),
        |p (h.val⁻¹ * x) - p x| := by
      apply Finset.sum_congr rfl
      intro h _
      simp only [defectMap_apply, Real.norm_eq_abs]
      apply tsum_eq_sum
      intro x hx
      rw [translation_difference_eq_zero_of_not_mem p h.val x hx, abs_zero]
    _ = ∑ h ∈ S, ∑ x ∈ p.support ∪ p.support.image (fun g => h * g),
        |p (h⁻¹ * x) - p x| :=
      Finset.sum_coe_sort S (fun h : G =>
        ∑ x ∈ p.support ∪ p.support.image (fun g => h * g),
          |p (h⁻¹ * x) - p x|)

/-- The actual image of finite nonnegative probabilities under the defect map. -/
def defectSet (S : Finset G) : Set (DefectSpace S) :=
  defectMap S '' {p : G →₀ ℝ | IsProbabilityWeights p}

theorem convex_defectSet (S : Finset G) : Convex ℝ (defectSet S) :=
  convex_probabilityWeights.linear_image (defectMap S)

theorem diracDefect_mem_defectSet (S : Finset G) (g : G) :
    diracDefect S g ∈ defectSet S := by
  refine ⟨Finsupp.single g 1, isProbabilityWeights_single g, ?_⟩
  simp

end ThompsonNonamenability

end

end OAI

end
end

section
section
namespace OAI

/-!
# Finite probabilities approximately invariant under a finite set

The usual positive normalized invariant mean forces zero to lie in the
closure of the actual finite-probability defect set. The separation argument
uses bounded coordinate functions of a continuous linear functional on ℓ¹;
no identification of the full dual of ℓ¹ is assumed.
-/

noncomputable section

open scoped ENNReal BigOperators


namespace ThompsonNonamenability

variable {G : Type uG} [Group G] [DecidableEq G]

local instance : Fact (1 ≤ (1 : ℝ≥0∞)) := ⟨le_rfl⟩

/-- A separator gives one bounded real function for each translation. -/
def separatorCoordinate {S : Finset G} (ell : DefectSpace S →L[ℝ] ℝ)
    (h : {h : G // h ∈ S}) : BoundedReal G :=
  ⟨fun g => ell (lp.single 1 (h, g) 1), memℓp_infty ⟨‖ell‖, by
    rintro y ⟨g, rfl⟩
    have hb := ell.le_opNorm (lp.single 1 (h, g) 1)
    simpa only [lp.norm_single (by norm_num : 0 < (1 : ℝ≥0∞)),
      norm_one, mul_one] using hb⟩⟩

omit [Group G] in
@[simp]
theorem separatorCoordinate_apply [Group G] {S : Finset G}
    (ell : DefectSpace S →L[ℝ] ℝ) (h : {h : G // h ∈ S}) (g : G) :
    separatorCoordinate ell h g = ell (lp.single 1 (h, g) 1) := rfl

/-- The finite sum whose mean vanishes by left invariance. -/
def separatorDefect {S : Finset G} (ell : DefectSpace S →L[ℝ] ℝ) : BoundedReal G :=
  ∑ h : {h : G // h ∈ S},
    (leftPull h.val (separatorCoordinate ell h) - separatorCoordinate ell h)

theorem separatorDefect_apply {S : Finset G} (ell : DefectSpace S →L[ℝ] ℝ)
    (g : G) : separatorDefect ell g = ell (diracDefect S g) := by
  classical
  cases Subsingleton.elim (inferInstance : DecidableEq G) (Classical.decEq G)
  simp only [separatorDefect, lp.coeFn_sum, Finset.sum_apply,
    lp.coeFn_sub, Pi.sub_apply, leftPull_apply, separatorCoordinate_apply,
    diracDefect, map_sum, map_sub]

theorem InvariantMean.separatorDefect_eq_zero (M : InvariantMean G)
    {S : Finset G} (ell : DefectSpace S →L[ℝ] ℝ) : M (separatorDefect ell) = 0 := by
  classical
  change M.toLinearMap (∑ h : {h : G // h ∈ S},
    (leftPull h.val (separatorCoordinate ell h) - separatorCoordinate ell h)) = 0
  simp only [map_sum, map_sub, M.left_invariant, sub_self, Finset.sum_const_zero]

/-- Separation contradicts the existence of a positive normalized invariant mean. -/
theorem InvariantMean.zero_mem_closure_defectSet (M : InvariantMean G)
    (S : Finset G) : (0 : DefectSpace S) ∈ closure (defectSet S) := by
  classical
  by_contra hout
  obtain ⟨ell, c, hc, hsep⟩ := geometric_hahn_banach_point_closed
    (convex_defectSet S).closure isClosed_closure hout
  have hcpos : 0 < c := by simpa only [ell.map_zero] using hc
  have hpoint (g : G) : c ≤ separatorDefect ell g := by
    rw [separatorDefect_apply]
    apply le_of_lt
    apply hsep
    apply subset_closure
    exact diracDefect_mem_defectSet S g
  have hmean : c ≤ M (separatorDefect ell) := by
    simpa only [InvariantMean.map_const] using
      M.mono (f := c • (1 : BoundedReal G)) (g := separatorDefect ell)
        (fun g => by simpa only [BoundedReal.smul_one_apply] using hpoint g)
  rw [M.separatorDefect_eq_zero] at hmean
  exact (not_le_of_gt hcpos) hmean

/-- Actual nonnegative finite probabilities with arbitrarily small total defect. -/
theorem InvariantMean.exists_probability_small_defect (M : InvariantMean G)
    (S : Finset G) {ε : ℝ} (hε : 0 < ε) :
    ∃ p : G →₀ ℝ, IsProbabilityWeights p ∧ ‖defectMap S p‖ < ε := by
  classical
  obtain ⟨v, hv, hvsmall⟩ := Metric.mem_closure_iff.mp
    (M.zero_mem_closure_defectSet S) ε hε
  obtain ⟨p, hp, rfl⟩ := hv
  refine ⟨p, hp, ?_⟩
  simpa only [dist_zero_left] using hvsmall

end ThompsonNonamenability

end

end OAI

end
end

section
section
namespace OAI

/-!
# Finite scalar levels

The distinct values of a nonnegative function on a finite set, together with
zero, give a finite subdivision. Its positive gaps reconstruct every value
and every absolute difference by strict superlevel indicators. These are
finite sums, including when the only level is zero.
-/

open scoped BigOperators


namespace ThompsonNonamenability

variable {G : Type uG}

/-- The actual ordered levels of `p` on `K`, with zero included. -/
structure FiniteLevelChain (K : Finset G) (p : G → ℝ) where
  n : ℕ
  value : Fin (n + 1) → ℝ
  value_zero : value 0 = 0
  strictMono_value : StrictMono value
  image_value_eq : Finset.univ.image value = insert 0 (K.image p)

namespace FiniteLevelChain

/-- Construct the level chain by sorting the actual finite image. -/
noncomputable def ofNonneg (K : Finset G) (p : G → ℝ)
    (hp : ∀ x ∈ K, 0 ≤ p x) : FiniteLevelChain K p := by
  classical
  let L : Finset ℝ := insert 0 (K.image p)
  have hpos : 0 < L.card := Finset.card_pos.mpr ⟨0, by simp [L]⟩
  let n := L.card - 1
  have hcard : L.card = n + 1 := by dsimp [n]; omega
  let e : Fin (n + 1) ↪o ℝ := L.orderEmbOfFin hcard
  have heimage : Finset.univ.image e = L :=
    Finset.image_orderEmbOfFin_univ L hcard
  have hnonneg : ∀ a ∈ L, 0 ≤ a := by
    intro a ha
    rcases Finset.mem_insert.mp ha with rfl | ha
    · exact le_rfl
    · rcases Finset.mem_image.mp ha with ⟨x, hx, rfl⟩
      exact hp x hx
  have hezero : e 0 = 0 := by
    have hz : (0 : ℝ) ∈ Finset.univ.image e := by
      rw [heimage]
      simp [L]
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hz
    apply le_antisymm
    · calc
        e 0 ≤ e j := e.monotone (Fin.zero_le j)
        _ = 0 := hj
    · exact hnonneg (e 0) (Finset.orderEmbOfFin_mem L hcard 0)
  exact ⟨n, e, hezero, e.strictMono, heimage⟩

theorem exists_chain (K : Finset G) (p : G → ℝ)
    (hp : ∀ x ∈ K, 0 ≤ p x) : Nonempty (FiniteLevelChain K p) :=
  ⟨ofNonneg K p hp⟩

variable {K : Finset G} {p : G → ℝ} (c : FiniteLevelChain K p)

/-- Width of the interval immediately above the indexed level. -/
def gap (i : Fin c.n) : ℝ := c.value i.succ - c.value i.castSucc

theorem gap_pos (i : Fin c.n) : 0 < c.gap i := by
  apply sub_pos.mpr
  exact c.strictMono_value (show i.castSucc < i.succ from Nat.lt_succ_self i.val)

/-- Telescoping below any selected value of a strictly increasing finite list. -/
private theorem telescope : ∀ (n : ℕ) (f : Fin (n + 1) → ℝ),
    StrictMono f → ∀ k : Fin (n + 1),
      f k - f 0 = ∑ i : Fin n,
        (f i.succ - f i.castSucc) * (if f i.castSucc < f k then 1 else 0) := by
  intro n
  induction n with
  | zero =>
      intro f hf k
      have hk : k = 0 := by
        apply Fin.ext
        have hklt := k.isLt
        omega
      subst k
      simp
  | succ n ih =>
      intro f hf k
      refine Fin.cases ?_ (fun k => ?_) k
      · have hnot : ∀ i : Fin (n + 1), ¬ f i.castSucc < f 0 := by
          intro i
          exact not_lt_of_ge (hf.monotone (Fin.zero_le i.castSucc))
        simp [hnot]
      · have hs := ih (fun j : Fin (n + 1) => f j.succ)
          (by intro a b hab; exact hf (Nat.succ_lt_succ hab)) k
        have hfirst : f 0 < f k.succ := hf (Fin.succ_pos k)
        rw [Fin.sum_univ_succ]
        change f k.succ - f 0 =
          (f (0 : Fin (n + 1)).succ - f 0) * (if f 0 < f k.succ then 1 else 0) +
            ∑ i : Fin n, (f i.succ.succ - f i.castSucc.succ) *
              (if f i.castSucc.succ < f k.succ then 1 else 0)
        rw [if_pos hfirst, mul_one, ← hs]
        ring

/-- The finite layer decomposition of each value in the actual level set. -/
theorem reconstruct (a : ℝ) (ha : a ∈ insert 0 (K.image p)) :
    a = ∑ i : Fin c.n, c.gap i *
      (if c.value i.castSucc < a then (1 : ℝ) else 0) := by
  classical
  have ha' : a ∈ Finset.univ.image c.value := by
    rw [c.image_value_eq]
    exact ha
  rcases Finset.mem_image.mp ha' with ⟨k, _, rfl⟩
  simpa only [gap, c.value_zero, sub_zero] using
    telescope c.n c.value c.strictMono_value k

private theorem abs_sub_eq_sum_of_le (a b : ℝ)
    (ha : a ∈ insert 0 (K.image p)) (hb : b ∈ insert 0 (K.image p))
    (hab : a ≤ b) :
    |a - b| = ∑ i : Fin c.n, c.gap i *
      |(if c.value i.castSucc < a then (1 : ℝ) else 0) -
        (if c.value i.castSucc < b then (1 : ℝ) else 0)| := by
  classical
  have hi : ∀ i : Fin c.n,
      (if c.value i.castSucc < a then (1 : ℝ) else 0) ≤
        (if c.value i.castSucc < b then (1 : ℝ) else 0) := by
    intro i
    by_cases hai : c.value i.castSucc < a
    · have hbi : c.value i.castSucc < b := lt_of_lt_of_le hai hab
      simp [hai, hbi]
    · simp only [if_neg hai]
      by_cases hbi : c.value i.castSucc < b <;> simp [hbi]
  calc
    |a - b| = b - a := by rw [abs_of_nonpos (sub_nonpos.mpr hab)]; ring
    _ = (∑ i : Fin c.n, c.gap i * (if c.value i.castSucc < b then (1 : ℝ) else 0)) -
        (∑ i : Fin c.n, c.gap i * (if c.value i.castSucc < a then (1 : ℝ) else 0)) :=
      congrArg₂ (fun x y : ℝ => x - y) (c.reconstruct b hb) (c.reconstruct a ha)
    _ = ∑ i : Fin c.n, c.gap i *
        |(if c.value i.castSucc < a then (1 : ℝ) else 0) -
          (if c.value i.castSucc < b then (1 : ℝ) else 0)| := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      rw [abs_of_nonpos (sub_nonpos.mpr (hi i))]
      ring

/-- The finite coarea identity for a scalar absolute difference. -/
theorem abs_sub_eq_sum (a b : ℝ)
    (ha : a ∈ insert 0 (K.image p)) (hb : b ∈ insert 0 (K.image p)) :
    |a - b| = ∑ i : Fin c.n, c.gap i *
      |(if c.value i.castSucc < a then (1 : ℝ) else 0) -
        (if c.value i.castSucc < b then (1 : ℝ) else 0)| := by
  rcases le_total a b with hab | hba
  · exact c.abs_sub_eq_sum_of_le a b ha hb hab
  · simpa only [abs_sub_comm] using c.abs_sub_eq_sum_of_le b a hb ha hba

end FiniteLevelChain

end ThompsonNonamenability

end OAI

end
end

section
section
namespace OAI

noncomputable section


namespace ThompsonNonamenability

open scoped BigOperators symmDiff

variable {G : Type uG} [DecidableEq G]

private theorem sum_indicator_eq_card (A C : Finset G) (hAC : A ⊆ C) :
    (∑ x ∈ C, if x ∈ A then (1 : ℝ) else 0) = (A.card : ℝ) := by
  classical
  have hfilter : C.filter (fun x => x ∈ A) = A := by
    ext x
    simp only [Finset.mem_filter]
    exact ⟨And.right, fun hx => ⟨hAC hx, hx⟩⟩
  rw [← Finset.sum_filter, hfilter]
  simp

private theorem sum_abs_indicators_eq_card_symmDiff
    (A B C : Finset G) (hAC : A ⊆ C) (hBC : B ⊆ C) :
    (∑ x ∈ C,
      |(if x ∈ A then (1 : ℝ) else 0) -
        (if x ∈ B then (1 : ℝ) else 0)|) = ((A ∆ B).card : ℝ) := by
  classical
  have hsub : A ∆ B ⊆ C := by
    intro x hx
    rcases Finset.mem_symmDiff.mp hx with hx | hx
    · exact hAC hx.1
    · exact hBC hx.1
  calc
    _ = ∑ x ∈ C, if x ∈ A ∆ B then (1 : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro x hx
      by_cases hA : x ∈ A <;> by_cases hB : x ∈ B <;>
        simp [hA, hB, Finset.mem_symmDiff]
    _ = _ := sum_indicator_eq_card (A ∆ B) C hsub

private theorem finite_value_mem {K : Finset G} {p : G → ℝ}
    (hpK : ∀ x, x ∉ K → p x = 0) (x : G) :
    p x ∈ insert 0 (K.image p) := by
  classical
  by_cases hx : x ∈ K
  · exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem p hx)
  · rw [hpK x hx]
    exact Finset.mem_insert_self _ _

namespace FiniteLevelChain

variable {K : Finset G} {p : G → ℝ}

/-- The strict superlevel set at the lower endpoint of a positive layer. -/
def levelSet (c : FiniteLevelChain K p) (i : Fin c.n) : Finset G := by
  classical
  exact K.filter (fun x => c.value i.castSucc < p x)

omit [DecidableEq G] in
theorem levelSet_subset [DecidableEq G] (c : FiniteLevelChain K p) (i : Fin c.n) :
    c.levelSet i ⊆ K := Finset.filter_subset _ _

/-- The finite carrier restriction does not change positive-threshold membership. -/
theorem mem_levelSet (c : FiniteLevelChain K p)
    (hpK : ∀ x, x ∉ K → p x = 0) (i : Fin c.n) (x : G) :
    x ∈ c.levelSet i ↔ c.value i.castSucc < p x := by
  classical
  have hv : 0 ≤ c.value i.castSucc := by
    simpa only [c.value_zero] using
      c.strictMono_value.monotone (Fin.zero_le i.castSucc)
  constructor
  · intro hx
    exact (Finset.mem_filter.mp hx).2
  · intro hx
    apply Finset.mem_filter.mpr
    refine ⟨?_, hx⟩
    by_contra hxK
    rw [hpK x hxK] at hx
    exact (not_lt_of_ge hv) hx

omit [DecidableEq G] in
theorem levelSet_nonempty [DecidableEq G] (c : FiniteLevelChain K p) (i : Fin c.n) :
    (c.levelSet i).Nonempty := by
  classical
  have hlt : c.value i.castSucc < c.value i.succ :=
    c.strictMono_value (by
      change i.val < i.val + 1
      exact Nat.lt_succ_self i.val)
  have hv : 0 ≤ c.value i.castSucc := by
    simpa only [c.value_zero] using
      c.strictMono_value.monotone (Fin.zero_le i.castSucc)
  have hpos : 0 < c.value i.succ := lt_of_le_of_lt hv hlt
  have hmem : c.value i.succ ∈ insert 0 (K.image p) := by
    rw [← c.image_value_eq]
    exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
  have himage : c.value i.succ ∈ K.image p :=
    (Finset.mem_insert.mp hmem).resolve_left (ne_of_gt hpos)
  obtain ⟨x, hxK, hpx⟩ := Finset.mem_image.mp himage
  refine ⟨x, Finset.mem_filter.mpr ⟨hxK, ?_⟩⟩
  rw [hpx]
  exact hlt

/-- Exact finite layer-cake identity for the mass. -/
theorem coarea_mass (c : FiniteLevelChain K p)
    (hpK : ∀ x, x ∉ K → p x = 0) :
    (∑ x ∈ K, p x) =
      ∑ i : Fin c.n, c.gap i * ((c.levelSet i).card : ℝ) := by
  classical
  calc
    _ = ∑ x ∈ K, ∑ i : Fin c.n, c.gap i *
        (if c.value i.castSucc < p x then (1 : ℝ) else 0) := by
      apply Finset.sum_congr rfl
      intro x hx
      exact c.reconstruct (p x) (finite_value_mem hpK x)
    _ = ∑ i : Fin c.n, ∑ x ∈ K, c.gap i *
        (if c.value i.castSucc < p x then (1 : ℝ) else 0) :=
      Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [← Finset.mul_sum]
      congr 1
      calc
        _ = ∑ x ∈ K, if x ∈ c.levelSet i then (1 : ℝ) else 0 := by
          apply Finset.sum_congr rfl
          intro x hx
          simp only [c.mem_levelSet hpK i x]
        _ = _ := sum_indicator_eq_card _ K (c.levelSet_subset i)

end FiniteLevelChain

section Translation

variable [Group G]

theorem mem_leftTranslate_iff (h : G) (A : Finset G) (x : G) :
    x ∈ leftTranslate h A ↔ h⁻¹ * x ∈ A := by
  constructor
  · intro hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    simpa using hy
  · intro hx
    exact Finset.mem_image.mpr ⟨h⁻¹ * x, hx, by simp⟩

namespace FiniteLevelChain

variable {K : Finset G} {p : G → ℝ}

/-- Exact coarea identity for one left translation, over its finite support carrier. -/
theorem coarea_translation (c : FiniteLevelChain K p)
    (hpK : ∀ x, x ∉ K → p x = 0) (h : G) :
    (∑ x ∈ K ∪ leftTranslate h K, |p (h⁻¹ * x) - p x|) =
      ∑ i : Fin c.n, c.gap i *
        ((leftTranslate h (c.levelSet i) ∆ c.levelSet i).card : ℝ) := by
  classical
  calc
    _ = ∑ x ∈ K ∪ leftTranslate h K, ∑ i : Fin c.n, c.gap i *
        |(if c.value i.castSucc < p (h⁻¹ * x) then (1 : ℝ) else 0) -
          (if c.value i.castSucc < p x then (1 : ℝ) else 0)| := by
      apply Finset.sum_congr rfl
      intro x hx
      exact c.abs_sub_eq_sum (p (h⁻¹ * x)) (p x)
        (finite_value_mem hpK _) (finite_value_mem hpK _)
    _ = ∑ i : Fin c.n, ∑ x ∈ K ∪ leftTranslate h K, c.gap i *
        |(if c.value i.castSucc < p (h⁻¹ * x) then (1 : ℝ) else 0) -
          (if c.value i.castSucc < p x then (1 : ℝ) else 0)| :=
      Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [← Finset.mul_sum]
      congr 1
      have hleft : leftTranslate h (c.levelSet i) ⊆ K ∪ leftTranslate h K := by
        intro x hx
        obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
        exact Finset.mem_union_right _
          (Finset.mem_image_of_mem (fun y => h * y) (c.levelSet_subset i hy))
      have hright : c.levelSet i ⊆ K ∪ leftTranslate h K := by
        intro x hx
        exact Finset.mem_union_left _ (c.levelSet_subset i hx)
      calc
        _ = ∑ x ∈ K ∪ leftTranslate h K,
            |(if x ∈ leftTranslate h (c.levelSet i) then (1 : ℝ) else 0) -
              (if x ∈ c.levelSet i then (1 : ℝ) else 0)| := by
          apply Finset.sum_congr rfl
          intro x hx
          simp only [mem_leftTranslate_iff, c.mem_levelSet hpK]
        _ = _ := sum_abs_indicators_eq_card_symmDiff _ _ _ hleft hright

/-- Summing the exact translation identities introduces no cardinality factor. -/
theorem coarea_sum (c : FiniteLevelChain K p)
    (hpK : ∀ x, x ∉ K → p x = 0) (S : Finset G) :
    (∑ h ∈ S, ∑ x ∈ K ∪ leftTranslate h K, |p (h⁻¹ * x) - p x|) =
      ∑ i : Fin c.n, c.gap i *
        (∑ h ∈ S, ((leftTranslate h (c.levelSet i) ∆ c.levelSet i).card : ℝ)) := by
  calc
    _ = ∑ h ∈ S, ∑ i : Fin c.n, c.gap i *
        ((leftTranslate h (c.levelSet i) ∆ c.levelSet i).card : ℝ) :=
      Finset.sum_congr rfl (fun h _ => c.coarea_translation hpK h)
    _ = _ := by
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum]

end FiniteLevelChain

/-- A nonempty level inside the supplied finite support has small total boundary. -/
theorem finite_folner_of_small_defect_subset
    {K S : Finset G} {p : G → ℝ} {ε : ℝ}
    (hp0 : ∀ g, 0 ≤ p g)
    (hpK : ∀ g, g ∉ K → p g = 0)
    (mass : ∑ g ∈ K, p g = 1)
    (hdef : (∑ h ∈ S, ∑ x ∈ K ∪ leftTranslate h K,
      |p (h⁻¹ * x) - p x|) < ε) :
    ∃ A : Finset G, A ⊆ K ∧ A.Nonempty ∧
      (∑ h ∈ S, ((leftTranslate h A ∆ A).card : ℝ)) < ε * (A.card : ℝ) := by
  classical
  obtain ⟨c⟩ := FiniteLevelChain.exists_chain K p (fun g _ => hp0 g)
  have hmass : (∑ i : Fin c.n, c.gap i * ((c.levelSet i).card : ℝ)) = 1 :=
    (c.coarea_mass hpK).symm.trans mass
  have hex : ∃ i : Fin c.n,
      (∑ h ∈ S, ((leftTranslate h (c.levelSet i) ∆ c.levelSet i).card : ℝ)) <
        ε * ((c.levelSet i).card : ℝ) := by
    by_contra hnone
    have hfail : ∀ i : Fin c.n, ε * ((c.levelSet i).card : ℝ) ≤
        ∑ h ∈ S, ((leftTranslate h (c.levelSet i) ∆ c.levelSet i).card : ℝ) :=
      fun i => le_of_not_gt (fun hi => hnone ⟨i, hi⟩)
    have hle : ε ≤ ∑ h ∈ S, ∑ x ∈ K ∪ leftTranslate h K,
        |p (h⁻¹ * x) - p x| := by
      calc
        ε = ε * ∑ i : Fin c.n, c.gap i * ((c.levelSet i).card : ℝ) := by
          rw [hmass, mul_one]
        _ = ∑ i : Fin c.n, c.gap i * (ε * ((c.levelSet i).card : ℝ)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          ring
        _ ≤ ∑ i : Fin c.n, c.gap i *
            (∑ h ∈ S, ((leftTranslate h (c.levelSet i) ∆ c.levelSet i).card : ℝ)) :=
          Finset.sum_le_sum (fun i _ =>
            mul_le_mul_of_nonneg_left (hfail i) (c.gap_pos i).le)
        _ = _ := (c.coarea_sum hpK S).symm
    exact (not_lt_of_ge hle) hdef
  obtain ⟨i, hi⟩ := hex
  exact ⟨c.levelSet i, c.levelSet_subset i, c.levelSet_nonempty i, hi⟩

/-- Finite probability with small total translation defect yields a finite Følner set. -/
theorem finite_folner_of_small_defect
    {K S : Finset G} {p : G → ℝ} {ε : ℝ}
    (hp0 : ∀ g, 0 ≤ p g)
    (hpK : ∀ g, g ∉ K → p g = 0)
    (mass : ∑ g ∈ K, p g = 1)
    (hdef : (∑ h ∈ S, ∑ x ∈ K ∪ leftTranslate h K,
      |p (h⁻¹ * x) - p x|) < ε) :
    ∃ A : Finset G, A.Nonempty ∧
      (∑ h ∈ S, ((leftTranslate h A ∆ A).card : ℝ)) < ε * (A.card : ℝ) := by
  obtain ⟨A, _, hA, hsmall⟩ := finite_folner_of_small_defect_subset hp0 hpK mass hdef
  exact ⟨A, hA, hsmall⟩

end Translation

end ThompsonNonamenability

end

end OAI

end
end

section
section
namespace OAI

noncomputable section

open scoped BigOperators symmDiff


namespace ThompsonNonamenability

variable {G : Type uG} [Group G] [DecidableEq G]

/-- A standard invariant mean yields a finite set with small total boundary. -/
theorem InvariantMean.exists_folner_total (M : InvariantMean G)
    (S : Finset G) {ε : ℝ} (hε : 0 < ε) :
    ∃ A : Finset G, A.Nonempty ∧
      (∑ h ∈ S, ((leftTranslate h A ∆ A).card : ℝ)) < ε * A.card := by
  classical
  cases Subsingleton.elim (inferInstance : DecidableEq G) (Classical.decEq G)
  obtain ⟨p, hp, hsmall⟩ := M.exists_probability_small_defect S hε
  have hmass : ∑ g ∈ p.support, p g = 1 := by
    simpa only [mass_apply] using hp.2
  have hdef : (∑ h ∈ S, ∑ x ∈ p.support ∪ leftTranslate h p.support,
      |p (h⁻¹ * x) - p x|) < ε := by
    simpa only [norm_defectMap, leftTranslate] using hsmall
  exact finite_folner_of_small_defect (p := fun g => p g) (K := p.support)
    (S := S) hp.1 (fun g hg => Finsupp.notMem_support_iff.mp hg) hmass hdef

/-- Finite Følner sets, with no countability or finite-generation assumption. -/
theorem InvariantMean.exists_folner (M : InvariantMean G)
    (S : Finset G) {ε : ℝ} (hε : 0 < ε) :
    ∃ A : Finset G, A.Nonempty ∧
      ∀ h ∈ S, ((leftTranslate h A ∆ A).card : ℝ) < ε * A.card := by
  obtain ⟨A, hA, htotal⟩ := M.exists_folner_total S hε
  refine ⟨A, hA, ?_⟩
  intro h hh
  have hone : ((leftTranslate h A ∆ A).card : ℝ) ≤
      ∑ g ∈ S, ((leftTranslate g A ∆ A).card : ℝ) :=
    Finset.single_le_sum (f := fun g => ((leftTranslate g A ∆ A).card : ℝ))
      (fun g _ => Nat.cast_nonneg _) hh
  exact hone.trans_lt htotal

/-- Uniform expansion of nonempty finite sets rules out a standard invariant mean. -/
theorem not_amenable_of_uniform_boundary (S : Finset G) {b : ℝ} (hb : 0 < b)
    (hexpand : ∀ A : Finset G, A.Nonempty →
      ∃ h ∈ S, b * A.card ≤ ((leftTranslate h A ∆ A).card : ℝ)) :
    ¬ Nonempty (InvariantMean G) := by
  rintro ⟨M⟩
  obtain ⟨A, hA, hsmall⟩ := M.exists_folner S hb
  obtain ⟨h, hh, hlarge⟩ := hexpand A hA
  exact not_le_of_gt (hsmall h hh) hlarge

end ThompsonNonamenability

end

end OAI

end
end

section
section
namespace OAI

noncomputable section

open scoped symmDiff

namespace ThompsonNonamenability

local instance : DecidableEq F := Classical.decEq F

theorem thompson_F_boundary_with_exact_constant :
    ∃ (D : ℕ) (S : Finset F),
      2 ≤ D ∧
      4 * Analytic.displacementLipschitzConstant ^ 2 / (1 / 2 : ℝ) ^ 2 <
        (D : ℝ) ∧
      S.Nonempty ∧
      0 < boundaryConstant Analytic.displacementLipschitzConstant (1 / 2) D ∧
      ∀ A : Finset F, A.Nonempty →
        ∃ h ∈ S,
          boundaryConstant Analytic.displacementLipschitzConstant (1 / 2) D ≤
            boundaryRatio A h := by
  obtain ⟨D, hD, hlarge⟩ :=
    exists_branching_parameter Analytic.displacementLipschitzConstant (1 / 2)
  obtain ⟨S, hS, hb, hboundary⟩ :=
    exists_fixed_boundary Analytic.displacementMap
      Analytic.displacementLipschitzConstant (1 / 2)
      Analytic.displacementLipschitzConstant_pos (by norm_num)
      Analytic.displacementMap_lipschitz Analytic.displacementMap_displacement
      D hD hlarge
  exact ⟨D, S, hD, hlarge, hS, hb, hboundary⟩

/-- A fixed finite subset of the genuine PL group uniformly expands every
nonempty finite subset, in the unnormalized symmetric-difference form. -/
theorem thompson_F_uniform_boundary :
    ∃ (S : Finset F) (b : ℝ), S.Nonempty ∧ 0 < b ∧
      ∀ A : Finset F, A.Nonempty →
        ∃ h ∈ S, b * (A.card : ℝ) ≤ ((leftTranslate h A ∆ A).card : ℝ) := by
  obtain ⟨D, S, _hD, _hlarge, hS, hb, hboundary⟩ :=
    thompson_F_boundary_with_exact_constant
  refine ⟨S, boundaryConstant Analytic.displacementLipschitzConstant (1 / 2) D,
    hS, hb, ?_⟩
  intro A hA
  obtain ⟨h, hh, hratio⟩ := hboundary A hA
  have hcard : (0 : ℝ) < (A.card : ℝ) :=
    Nat.cast_pos.mpr (Finset.card_pos.mpr hA)
  refine ⟨h, hh, ?_⟩
  change boundaryConstant Analytic.displacementLipschitzConstant (1 / 2) D ≤
    ((leftTranslate h A ∆ A).card : ℝ) / (A.card : ℝ) at hratio
  exact (le_div_iff₀ hcard).mp hratio

/-- Standard Thompson F admits no positive normalized left-invariant mean on
all bounded real functions. The carrier is identified with the ordinary
finite-breakpoint dyadic PL homeomorphisms by `F.standardPLEquiv`. -/
theorem thompson_F_not_amenable : ¬ Nonempty (InvariantMean F) := by
  obtain ⟨S, b, _hS, hb, hboundary⟩ := thompson_F_uniform_boundary
  exact not_amenable_of_uniform_boundary S hb hboundary

end ThompsonNonamenability

end

end OAI

end
end

section
section
/-! Transfer of OpenAI's `thompson_F_not_amenable` (OpenAI Math Release, "Thompson's group F
is nonamenable", https://github.com/openai/math) to the published `CannonFloydParry.F` and
`Garrido.IsAmenable`. -/

namespace ThompsonAmenability.OAIBridge

open OAI.ThompsonNonamenability
open scoped Pointwise

/-- Amenability transfers backwards along a group isomorphism. -/
theorem isAmenable_of_mulEquiv {G H : Type*} [Group G] [Group H] (e : H ≃* G)
    (hG : Garrido.IsAmenable G) : Garrido.IsAmenable H := by
  obtain ⟨m, ⟨h0, hadd⟩, h1, hinv⟩ := hG
  refine ⟨fun s => m (e '' s), ⟨by simpa using h0, ?_⟩, ?_, ?_⟩
  · intro s t hst
    simp only [Set.image_union]
    exact hadd _ _ ((Set.disjoint_image_iff e.injective).2 hst)
  · simpa [Set.image_univ_of_surjective e.surjective] using h1
  · intro g s
    show m (e '' (g • s)) = m (e '' s)
    rw [show e '' (g • s) = e g • (e '' s) from Set.image_smul_distrib e g s]
    exact hinv _ _

/-- An element of OpenAI's `F` as an order isomorphism of the unit interval. -/
noncomputable def toOrderIso (g : F) : CannonFloydParry.UI ≃o CannonFloydParry.UI :=
  StrictMono.orderIsoOfSurjective (fun x => g x) g.strictMono
    (fun y => ⟨g.toHomeomorph.symm y, g.toHomeomorph.apply_symm_apply y⟩)

@[simp] theorem toOrderIso_apply (g : F) (x : CannonFloydParry.UI) :
    toOrderIso g x = g x := rfl

theorem isThompson_toOrderIso (g : F) : CannonFloydParry.IsThompson (toOrderIso g) := by
  classical
  let w := g.witness
  refine ⟨Finset.univ.image (fun i => (w.knots i : ℝ)), ?_, ?_⟩
  · intro b hb
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hb
    obtain ⟨k, n, hk⟩ := w.dyadic i
    exact ⟨k, n, hk⟩
  · intro x y hxy hB
    have hx0 := x.2.1
    have hy1 := y.2.2
    let mid : CannonFloydParry.UI :=
      ⟨((x : ℝ) + y) / 2, by constructor <;> linarith⟩
    have hmx : (x : ℝ) < mid := by show (x : ℝ) < ((x : ℝ) + y) / 2; linarith
    have hmy : (mid : ℝ) < y := by show ((x : ℝ) + y) / 2 < y; linarith
    obtain ⟨i, hi1, hi2⟩ := w.cover mid
    have hi1' : (w.knots i.castSucc : ℝ) ≤ mid := hi1
    have hi2' : (mid : ℝ) ≤ w.knots i.succ := hi2
    have hkx : (w.knots i.castSucc : ℝ) ≤ x := by
      by_contra h
      push Not at h
      have hmem : (w.knots i.castSucc : ℝ) ∈ Set.Ioo (x : ℝ) y ∩
          ((Finset.univ.image (fun i => (w.knots i : ℝ)) : Finset ℝ) : Set ℝ) :=
        ⟨⟨h, lt_of_le_of_lt hi1' hmy⟩, by simp⟩
      rw [hB] at hmem
      exact hmem
    have hky : (y : ℝ) ≤ w.knots i.succ := by
      by_contra h
      push Not at h
      have hmem : (w.knots i.succ : ℝ) ∈ Set.Ioo (x : ℝ) y ∩
          ((Finset.univ.image (fun i => (w.knots i : ℝ)) : Finset ℝ) : Set ℝ) :=
        ⟨⟨lt_of_lt_of_le hmx hi2', h⟩, by simp⟩
      rw [hB] at hmem
      exact hmem
    refine ⟨w.exponent i,
      (g (w.knots i.castSucc) : ℝ) - 2 ^ w.exponent i * (w.knots i.castSucc : ℝ), ?_⟩
    intro z hz
    have h := w.affine i z (le_trans hkx hz.1) (le_trans hz.2 hky)
    rw [toOrderIso_apply]
    change (g.toIntervalHomeomorph z : ℝ) = _
    rw [h]
    ring

/-- OpenAI's `F` embeds in the published `CannonFloydParry.F`. -/
noncomputable def embed : F →* CannonFloydParry.F :=
  MonoidHom.mk' (fun g => ⟨toOrderIso g, Subgroup.subset_closure (isThompson_toOrderIso g)⟩)
    (fun h g => by
      apply Subtype.ext
      ext x
      rfl)

theorem embed_injective : Function.Injective embed := by
  intro g h hgh
  apply F.ext
  intro x
  have := congrArg (fun k : CannonFloydParry.F =>
    ((k : CannonFloydParry.UI ≃o CannonFloydParry.UI) x)) hgh
  exact this

theorem not_isAmenable_F : ¬ Garrido.IsAmenable CannonFloydParry.F := by
  intro hA
  have hR : Garrido.IsAmenable embed.range := Garrido.isAmenable_subgroup hA _
  have hF : Garrido.IsAmenable F :=
    isAmenable_of_mulEquiv (MonoidHom.ofInjective embed_injective) hR
  obtain ⟨m, hpos, hnorm, hinv⟩ := ((Garrido.isAmenable_tfae F).out 0 1).1 hF
  apply thompson_F_not_amenable
  refine ⟨⟨m, hpos, hnorm 1 (fun _ => rfl), fun h f => ?_⟩⟩
  have : leftPull h f = Garrido.lshift h⁻¹ f := by
    apply lp.ext
    funext g
    simp [leftPull, Garrido.lshift]
  rw [this]
  exact hinv _ _

end ThompsonAmenability.OAIBridge

end
end

section
open ThompsonAmenability

theorem solution : ¬ Garrido.IsAmenable CannonFloydParry.F := by
  exact ThompsonAmenability.OAIBridge.not_isAmenable_F

end
