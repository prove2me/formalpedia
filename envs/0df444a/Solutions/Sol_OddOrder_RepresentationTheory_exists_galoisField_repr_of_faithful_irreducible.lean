-- Prove2me | solution 1 for OddOrder.RepresentationTheory.exists_galoisField_repr_of_faithful_irreducible
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T04:45:21.956278+00:00
-- url     : https://prove2.me/submissions/5bba0d0f-a6f3-4eaa-af86-871e2cce9cf7

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/GroupTheory/RepresentationTheory/SingerField.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_SingerField
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.GroupWithZero.Units.Fintype
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.RepresentationTheory.Maschke
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.NumberTheory.Multiplicity
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Algebra.Order.Ring.GeomSum
import Mathlib.Algebra.Ring.GeomSum

-- ===== OddOrder/GroupTheory/RepresentationTheory/SingerField.lean =====
namespace OddOrder.RepresentationTheory

universe u

variable {p : ℕ} {C M : Type u} [CommGroup C] [AddCommGroup M]
  [Module (MonoidAlgebra (ZMod p) C) M]

namespace SingerFieldData

/-- The additive isomorphism transports cardinality: `|K| = |M|`. -/
theorem card_K_eq [Fintype M] (data : SingerFieldData (p := p) (C := C) (M := M)) :
    Fintype.card data.K = Fintype.card M :=
  (Fintype.card_congr data.e.toEquiv).symm

/-- When `|M| = p ^ n` (`n ≠ 0`), the Singer field `K` is the Galois field `GF(p^n)`.
This is the form consumed by Peterfalvi's finite-field model, in which the elementary
abelian `P` (`|P| = p^q`) is identified with the additive group of `GF(p^q)`. -/
theorem nonempty_ringEquiv_galoisField [Fact p.Prime] [Fintype M] {n : ℕ} (hn : n ≠ 0)
    (data : SingerFieldData (p := p) (C := C) (M := M)) (hcard : Fintype.card M = p ^ n) :
    Nonempty (data.K ≃+* GaloisField p n) := by
  have : Fintype (GaloisField p n) := Fintype.ofFinite _
  refine ⟨FiniteField.ringEquivOfCardEq ?_⟩
  rw [data.card_K_eq, hcard, ← Nat.card_eq_fintype_card, GaloisField.card p n hn]

end SingerFieldData

/-- **Singer mechanism (abelian case).**  If the finite abelian group `C` acts
`𝔽_p`-linearly and irreducibly (`M` is simple over `𝔽_p[C]`) on the finite module `M`,
then `M` is a field and `C` acts by multiplication: there is a `SingerFieldData`.

The construction: a simple module over the *commutative* ring `R = 𝔽_p[C]` is `R ⧸ I`
for a maximal ideal `I` (`isSimpleModule_iff_quot_maximal`), and `R ⧸ I` is a field
because `R` is commutative (`Ideal.Quotient.field`).  Under the additive identification
`M ≃+ R ⧸ I`, the action of `MonoidAlgebra.of _ _ c` is multiplication by the unit
`mk (of c)`. -/
theorem nonempty_singerFieldData [Finite M]
    [IsSimpleModule (MonoidAlgebra (ZMod p) C) M] :
    Nonempty (SingerFieldData (p := p) (C := C) (M := M)) := by
  classical
  obtain ⟨I, hImax, ⟨lequiv⟩⟩ :=
    (isSimpleModule_iff_quot_maximal (R := MonoidAlgebra (ZMod p) C) (M := M)).mp ‹_›
  have : I.IsMaximal := hImax
  let : Field (MonoidAlgebra (ZMod p) C ⧸ I) := Ideal.Quotient.field I
  have : Finite (MonoidAlgebra (ZMod p) C ⧸ I) := Finite.of_equiv _ lequiv.toEquiv
  let : Fintype (MonoidAlgebra (ZMod p) C ⧸ I) := Fintype.ofFinite _
  refine ⟨{
    K := MonoidAlgebra (ZMod p) C ⧸ I
    e := lequiv.toAddEquiv
    μ := (Units.map
            (Ideal.Quotient.mk I : MonoidAlgebra (ZMod p) C →+* _).toMonoidHom).comp
          (MonoidAlgebra.of (ZMod p) C).toHomUnits
    compat := ?_ }⟩
  intro c m
  change lequiv (MonoidAlgebra.of (ZMod p) C c • m) = _
  rw [map_smul, Algebra.smul_def, Ideal.Quotient.algebraMap_eq]
  rfl

section Irreducibility

variable {p : ℕ} [Fact p.Prime] {C M : Type u}
  [CommGroup C] [IsCyclic C] [Finite C]
  [AddCommGroup M] [Module (MonoidAlgebra (ZMod p) C) M] [Finite M]

omit [IsCyclic C] [Finite C] in
/-- **Galois-field realization of a faithful irreducible abelian action.**

If a commutative group `C` acts faithfully and irreducibly on a finite
`F_p[C]`-module `M` of order `p^q`, then `M` is additively `GF(p^q)` and
the action is multiplication through an injective homomorphism
`C → GF(p^q)ˣ`.

Unlike `exists_galoisField_repr`, this theorem takes irreducibility directly
as an `IsSimpleModule` instance and imposes no order condition on `C`.  This
is the branch-independent Singer entry used by Peterfalvi (9.7.b), including
the divided-order branch needed in (14.6). -/
theorem _root_.solution {q : ℕ} (hq : q ≠ 0)
    [IsSimpleModule (MonoidAlgebra (ZMod p) C) M]
    (hcardM : Nat.card M = p ^ q)
    (hfaith : ∀ c : C, (∀ x : M, MonoidAlgebra.of (ZMod p) C c • x = x) → c = 1) :
    ∃ (e : M ≃+ GaloisField p q) (μ : C →* (GaloisField p q)ˣ),
      Function.Injective μ ∧
      ∀ (c : C) (x : M),
        e (MonoidAlgebra.of (ZMod p) C c • x) = (μ c : GaloisField p q) * e x := by
  classical
  have : Fintype M := Fintype.ofFinite _
  obtain ⟨data⟩ := nonempty_singerFieldData (p := p) (C := C) (M := M)
  obtain ⟨φ⟩ := data.nonempty_ringEquiv_galoisField hq
    (by rw [← Nat.card_eq_fintype_card, hcardM])
  refine ⟨data.e.trans φ.toAddEquiv,
    (Units.map (φ : data.K →+* GaloisField p q).toMonoidHom).comp data.μ, ?_, ?_⟩
  · -- Faithfulness turns the multiplicative realization into an embedding.
    rw [injective_iff_map_eq_one]
    intro c hc
    apply hfaith c
    intro x
    have hcoe : φ ((data.μ c : data.K)) = 1 := by
      have := congrArg (Units.val) hc
      simpa [Units.coe_map] using this
    have hdμ : (data.μ c : data.K) = 1 := by
      have := φ.injective (hcoe.trans (map_one φ).symm)
      exact this
    have hcompat := data.compat c x
    rw [hdμ, one_mul] at hcompat
    exact data.e.injective hcompat
  · intro c x
    have hμc : ((((Units.map (φ : data.K →+* GaloisField p q).toMonoidHom).comp data.μ) c :
        (GaloisField p q)ˣ) : GaloisField p q) = φ ((data.μ c : data.K)) := by
      simp [Units.coe_map]
    calc (data.e.trans φ.toAddEquiv) (MonoidAlgebra.of (ZMod p) C c • x)
        = φ (data.e (MonoidAlgebra.of (ZMod p) C c • x)) := rfl
      _ = φ ((data.μ c : data.K) * data.e x) := by rw [data.compat c x]
      _ = φ ((data.μ c : data.K)) * φ (data.e x) := map_mul _ _ _
      _ = (((Units.map (φ : data.K →+* GaloisField p q).toMonoidHom).comp data.μ) c :
            GaloisField p q) * (data.e.trans φ.toAddEquiv) x := by rw [hμc]; rfl

end Irreducibility

end OddOrder.RepresentationTheory
