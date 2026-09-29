-- Prove2me | solution 1 for Rosenblatt.isVirtuallyNilpotent_of_isPolycyclic_of_abelian_isMulTorsionFree_isNilpotent_quotient_of_not_hasFreeSubsemigroupOfRankTwo
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-24T19:27:39.457893+00:00
-- url     : https://prove2.me/submissions/5b834754-5d93-45ea-9c02-7137f2005d5b

import Theorems.Thm_GroupFiniteness_fg_of_extension
import Definitions.Def_MilnorWolf_Growth
import Mathlib
import Definitions.Def_Chou_Growth
import Theorems.Thm_Rosenblatt_hasFreeSubsemigroupOfRankTwo_of_exists_eigenvalue_norm_ne_one
import Theorems.Thm_Rosenblatt_isVirtuallyNilpotent_of_isPolycyclic_of_isNilpotent_quotient_of_forall_eigenvalue_norm_eq_one

/-!
# Polycyclic groups (Wolf, Proposition 4.1 (1), p. 433)

Basic closure properties of `MilnorWolf.IsPolycyclic`: trivial groups and cyclic groups are
polycyclic, the notion is invariant under isomorphism, finitely generated abelian groups are
polycyclic, and an extension of a polycyclic group by a polycyclic group is polycyclic
(Rosenblatt's Remark 4.3).  Polycyclic groups are finitely generated and finitely presented.

The `Fin (t + 1)`-indexed normal series of the published definition is replaced, for the duration
of the proofs, by the `ℕ`-indexed characterisation `MilnorWolf.Lib.IsPolyChain`: a chain
`A : ℕ → Subgroup G` with `A 0 = ⊤`, eventually `⊥`, and each step normal with cyclic quotient.
-/

universe u v

namespace MilnorWolf
namespace Lib

open Function Subgroup

/-! ### One step of a normal series -/

/-- One step `H ⊆ K` of a normal series: `H ≤ K`, `H` is normal in `K`, and `K/H` is cyclic. -/
def IsCyclicStep {G : Type*} [Group G] (H K : Subgroup G) : Prop :=
  H ≤ K ∧ ∃ _ : (H.subgroupOf K).Normal, IsCyclic (K ⧸ H.subgroupOf K)

/-- Transport of "normal with cyclic quotient" along a surjection, by pulling the subgroup back. -/
theorem normal_isCyclic_comap {A B : Type*} [Group A] [Group B] (φ : A →* B)
    (hφ : Surjective φ) {Q : Subgroup B} (hn : Q.Normal) (hc : IsCyclic (B ⧸ Q)) :
    ∃ _ : (Q.comap φ).Normal, IsCyclic (A ⧸ Q.comap φ) := by
  have : Q.Normal := hn
  have hn' : (Q.comap φ).Normal := hn.comap φ
  refine ⟨hn', ?_⟩
  have hker : Q.comap φ = ((QuotientGroup.mk' Q).comp φ).ker := by
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
  have hs : Surjective ((QuotientGroup.mk' Q).comp φ) :=
    (QuotientGroup.mk'_surjective Q).comp hφ
  have e : A ⧸ Q.comap φ ≃* B ⧸ Q :=
    (QuotientGroup.quotientMulEquivOfEq hker).trans
      (QuotientGroup.quotientKerEquivOfSurjective _ hs)
  exact isCyclic_of_surjective e.symm e.symm.surjective

/-- The restriction of `f : G →* H` to the preimage of `K`. -/
def restrictComap {G H : Type*} [Group G] [Group H] (f : G →* H) (K : Subgroup H) :
    ↥(K.comap f) →* ↥K :=
  (f.comp (K.comap f).subtype).codRestrict K (fun x => Subgroup.mem_comap.mp x.2)

@[simp] theorem restrictComap_coe {G H : Type*} [Group G] [Group H] (f : G →* H) (K : Subgroup H)
    (x : ↥(K.comap f)) : ((restrictComap f K x : ↥K) : H) = f (x : G) := rfl

theorem restrictComap_surjective {G H : Type*} [Group G] [Group H] {f : G →* H}
    (hf : Surjective f) (K : Subgroup H) : Surjective (restrictComap f K) := by
  rintro ⟨y, hy⟩
  obtain ⟨x, rfl⟩ := hf y
  exact ⟨⟨x, by simpa using hy⟩, rfl⟩

/-- A step of a normal series pulls back along a surjection. -/
theorem IsCyclicStep.comap {G H : Type*} [Group G] [Group H] {f : G →* H} (hf : Surjective f)
    {K₂ K₁ : Subgroup H} (h : IsCyclicStep K₂ K₁) :
    IsCyclicStep (K₂.comap f) (K₁.comap f) := by
  obtain ⟨hle, hnorm, hcyc⟩ := h
  refine ⟨Subgroup.comap_mono hle, ?_⟩
  have hkey : (K₂.subgroupOf K₁).comap (restrictComap f K₁) =
      (K₂.comap f).subgroupOf (K₁.comap f) := by
    ext x
    simp [Subgroup.mem_subgroupOf]
  have := normal_isCyclic_comap (restrictComap f K₁) (restrictComap_surjective hf K₁)
    hnorm hcyc
  rwa [hkey] at this

/-- A step of a normal series pushes forward along an injection. -/
theorem IsCyclicStep.map {G H : Type*} [Group G] [Group H] {f : G →* H} (hf : Injective f)
    {H₂ H₁ : Subgroup G} (h : IsCyclicStep H₂ H₁) :
    IsCyclicStep (H₂.map f) (H₁.map f) := by
  obtain ⟨hle, hnorm, hcyc⟩ := h
  refine ⟨Subgroup.map_mono hle, ?_⟩
  have hcoe : ∀ x : ↥(H₁.map f),
      f (((Subgroup.equivMapOfInjective H₁ f hf).symm x : ↥H₁) : G) = (x : H) := by
    intro x
    conv_rhs => rw [← MulEquiv.apply_symm_apply (Subgroup.equivMapOfInjective H₁ f hf) x]
    exact (Subgroup.coe_equivMapOfInjective_apply H₁ f hf _).symm
  have hkey : (H₂.subgroupOf H₁).comap
      ((Subgroup.equivMapOfInjective H₁ f hf).symm : ↥(H₁.map f) →* ↥H₁) =
      (H₂.map f).subgroupOf (H₁.map f) := by
    ext x
    simp only [Subgroup.mem_comap, Subgroup.mem_subgroupOf]
    rw [← hcoe x]
    exact (Subgroup.mem_map_iff_mem hf).symm
  have := normal_isCyclic_comap
    ((Subgroup.equivMapOfInjective H₁ f hf).symm : ↥(H₁.map f) →* ↥H₁)
    (Subgroup.equivMapOfInjective H₁ f hf).symm.surjective hnorm hcyc
  rwa [hkey] at this

theorem IsCyclicStep.congr {G : Type*} [Group G] {H K H' K' : Subgroup G} (h : IsCyclicStep H K)
    (e₁ : H = H') (e₂ : K = K') : IsCyclicStep H' K' := e₁ ▸ e₂ ▸ h

/-- The trivial step `⊥ ⊆ ⊥`. -/
theorem isCyclicStep_of_eq_bot {G : Type*} [Group G] {H K : Subgroup G} (hH : H = ⊥)
    (hK : K = ⊥) : IsCyclicStep H K := by
  subst hH; subst hK
  have hn : ((⊥ : Subgroup G).subgroupOf ⊥).Normal := by
    rw [Subgroup.subgroupOf_bot_eq_top]; infer_instance
  exact ⟨le_rfl, hn,
    isCyclic_of_surjective (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)⟩

/-! ### An `ℕ`-indexed characterisation of `IsPolycyclic` -/

/-- A normal series of `G` indexed by `ℕ`: `A 0 = ⊤`, some `A t = ⊥`, and every step
`A (i+1) ⊆ A i` is normal with cyclic quotient. -/
def IsPolyChain {G : Type*} [Group G] (A : ℕ → Subgroup G) : Prop :=
  A 0 = ⊤ ∧ (∃ t, A t = ⊥) ∧ ∀ i, IsCyclicStep (A (i + 1)) (A i)

theorem isPolycyclic_of_chain {G : Type*} [Group G] {A : ℕ → Subgroup G} (h : IsPolyChain A) :
    IsPolycyclic G := by
  obtain ⟨h0, ⟨t, ht⟩, hstep⟩ := h
  exact ⟨t, fun i => A i.val, h0, ht, fun i => hstep i.val⟩

theorem exists_chain_of_isPolycyclic {G : Type*} [Group G] (h : IsPolycyclic G) :
    ∃ A : ℕ → Subgroup G, IsPolyChain A := by
  obtain ⟨t, A, h0, hlast, hstep⟩ := h
  have hbot : ∀ m, t ≤ m →
      A ⟨min m t, Nat.lt_succ_of_le (min_le_right m t)⟩ = ⊥ := by
    intro m hm
    rw [← hlast]
    exact congrArg A (Fin.ext (by simp [Fin.val_last]; omega))
  refine ⟨fun n => A ⟨min n t, Nat.lt_succ_of_le (min_le_right n t)⟩, ?_, ⟨t, ?_⟩, ?_⟩
  · rw [← h0]; exact congrArg A (Fin.ext (by simp))
  · exact hbot t le_rfl
  · intro i
    rcases lt_or_ge i t with hi | hi
    · refine IsCyclicStep.congr (hstep ⟨i, hi⟩) (congrArg A (Fin.ext ?_))
        (congrArg A (Fin.ext ?_))
      · simp only [Fin.val_succ]; omega
      · simp only [Fin.val_castSucc]; omega
    · exact isCyclicStep_of_eq_bot (hbot (i + 1) (by omega)) (hbot i hi)

/-! ### The basic examples -/

/-! ### Extensions -/

/-! ### Finitely generated abelian groups -/

/-! ### Polycyclic groups are finitely generated -/

theorem fg_of_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B) (h : Group.FG A) :
    Group.FG B := by
  have := h
  exact Group.fg_of_surjective (f := (e : A →* B)) (fun b => ⟨e.symm b, by simp⟩)

theorem fg_of_isCyclic {C : Type*} [Group C] [IsCyclic C] : Group.FG C := by
  obtain ⟨g, hg⟩ := ‹IsCyclic C›.exists_generator
  refine Group.fg_iff.mpr ⟨{g}, ?_, Set.finite_singleton g⟩
  rw [← Subgroup.zpowers_eq_closure]
  exact eq_top_iff.2 fun x _ => hg x

/-- `Group.FG` is closed under extensions. -/
theorem fg_of_extension {G : Type*} [Group G] (N : Subgroup G) [N.Normal]
    (hN : Group.FG N) (hQ : Group.FG (G ⧸ N)) : Group.FG G :=
  by haveI := hN; haveI := hQ; exact GroupFiniteness.fg_of_extension N


/-- A polycyclic group is finitely generated. -/
theorem fg_of_isPolycyclic {G : Type*} [Group G] (h : IsPolycyclic G) : Group.FG G := by
  obtain ⟨A, h0, ⟨t, ht⟩, hstep⟩ := exists_chain_of_isPolycyclic h
  have key : ∀ j : ℕ, Group.FG ↥(A (t - j)) := by
    intro j
    induction j with
    | zero =>
      rw [Nat.sub_zero, ht]
      exact (Group.fg_iff_subgroup_fg _).mpr Subgroup.FG.bot
    | succ j ihj =>
      rcases le_or_gt t j with hj | hj
      · have hjj : t - (j + 1) = t - j := by omega
        rw [hjj]; exact ihj
      · have he : t - j = (t - (j + 1)) + 1 := by omega
        rw [he] at ihj
        set i := t - (j + 1) with hi
        obtain ⟨hle, hnorm, hcyc⟩ := hstep i
        have hFGP : Group.FG ↥((A (i + 1)).subgroupOf (A i)) :=
          fg_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hle).symm ihj
        have hn := hnorm
        have hc := hcyc
        have hFGQ : Group.FG (↥(A i) ⧸ (A (i + 1)).subgroupOf (A i)) := fg_of_isCyclic
        exact fg_of_extension ((A (i + 1)).subgroupOf (A i)) hFGP hFGQ
  have hfg0 : Group.FG ↥(A 0) := by simpa using key t
  rw [h0] at hfg0
  exact fg_of_mulEquiv Subgroup.topEquiv hfg0

/-! ### Polycyclic groups are finitely presented -/

end Lib
end MilnorWolf

/-!
# Rosenblatt, Corollary 2.5: a ping-pong criterion for free subsemigroups

*Invariant measures and growth conditions*, Trans. Amer. Math. Soc. 193 (1974), Proposition 2.4
(p. 36) and Corollary 2.5 (p. 37).

If some nonempty `A ⊆ G` satisfies `aA ∪ bA ⊆ A` with `aA` and `bA` disjoint, then `a` and `b`
generate a free subsemigroup.  This is the tool Theorem 4.17 uses to build a free subsemigroup
out of a matrix eigenvalue off the unit circle, and it is the only place in that argument where
freeness is actually established.

Rosenblatt's Proposition 2.4 is the sharper statement: from `aA ∪ bA ⊆ A` alone, *either* `a` and
`b` generate a free subsemigroup *or* some `z` in the subsemigroup they generate has
`zA ⊆ aA ∩ bA`.  Disjointness kills the second alternative because `A` is nonempty, which is
exactly how Corollary 2.5 follows.  The proof below inlines that dichotomy rather than splitting
it out, and the place it appears is `lift_ne_one`: a nonempty word equal to `1` forces
`A ⊆ (a or b)A`, and then the *other* letter's translate lands in both translates at once.

The conclusion is stated for the given pair `a`, `b` — Rosenblatt's "in this case `a`, `b`
generate a free subsemigroup" — which is stronger than the bare existence statement
`Chou.HasFreeSubsemigroupOfRankTwo`, and is what Theorem 4.17 needs, since it produces a
specific pair.
-/

namespace Rosenblatt

end Rosenblatt

/-!
# Rosenblatt, Theorem 4.17 (p. 47)

*Invariant measures and growth conditions*, Trans. Amer. Math. Soc. 193 (1974).

Given an extension `e → ℤ^r → G → H → e`, if conjugation by some `g ∈ G` acts on `ℤ^r` with an
eigenvalue off the unit circle, then `G` has a free subsemigroup on two generators.

This file builds the two ingredients Rosenblatt's proof uses besides Corollary 2.5.

* **Lemma 4.16** (p. 46): if `|x| ≥ 3` then two `±1`-coefficient combinations of distinct
  positive powers of `x` agree only if they are the same combination.  Equivalently — and this
  is the form Theorem 4.17 actually uses, where it concludes that two polynomials "are
  identical" — a nonzero polynomial whose coefficients all lie in `{-1, 0, 1}` has no complex
  root of modulus `≥ 3`.  In Mathlib this is a corollary of Cauchy's bound on the roots: the
  bound is `(sup of the lower coefficients)/(leading coefficient) + 1`, which for such a
  polynomial is at most `2`.

* **Lemma 4.15** (p. 46): for a real `n × n` matrix `T` with eigenvalue `φ`, there are constants
  `K₁, …, Kₙ ∈ ℂ`, not all zero, such that any relation `∑ Pᵢ(T) aᵢ = ∑ Qᵢ(T) aᵢ` between
  polynomial combinations of the standard basis forces `∑ Pᵢ(φ) Kᵢ = ∑ Qᵢ(φ) Kᵢ`.  The
  constants are the coordinates of an eigenvector of the transpose.

Neither is published as its own leaf: 4.16 is a short consequence of a Mathlib bound, and 4.15
is linear algebra local to this argument.  The published leaf is Corollary 2.5, which is the
general tool, and Theorem 4.17 itself.
-/

namespace Rosenblatt

open Polynomial
open scoped Matrix

/-! ### Lemma 4.16 -/

/-! ### Lemma 4.15 -/

end Rosenblatt

/-!
# Theorem 4.17: the group-theoretic infrastructure

Rosenblatt, p. 47.  Setting: a group `G` with a normal subgroup `A` isomorphic to `ℤ^r`, an
element `g`, and an integer matrix `T` giving conjugation by `g` in coordinates.

Two facts carry all the group theory of the proof; the rest is polynomial bookkeeping.

* `pow_mul_emb` — conjugation iterated: `gᵏ · ι(w) = ι(Tᵏ w) · gᵏ`.  This is what lets the
  computation push every `g` to the right and collect the abelian parts, which is how
  Rosenblatt's set `𝒜` is closed under left multiplication by his `x` and `y`.
* `pow_matrix_eq_one_of_mem` — if some power of `g` lands in `A`, then that power of `T` is the
  identity.  Conjugation by an element of `A` is trivial on `A`, because `A` is abelian; so
  `T ^ M` acts as the identity and injectivity of the embedding finishes it.  Rosenblatt uses
  this in a single clause ("since otherwise there is some `M ≥ 1` with `g^M ∈ ℤ^r` and thus
  `r_g` would have all eigenvalues of absolute value 1"), and `norm_eq_one_of_pow_eq_one` draws
  the consequence for the eigenvalue.
-/

namespace Rosenblatt

open scoped Matrix

section Emb

variable {G : Type*} [Group G] {r : ℕ} (A : Subgroup G)
  (e : A ≃* Multiplicative (Fin r → ℤ))

/-- The embedding of `ℤ^r` into `G` determined by the isomorphism. -/
def emb (z : Fin r → ℤ) : G := ((e.symm (Multiplicative.ofAdd z) : A) : G)

theorem emb_mem (z : Fin r → ℤ) : emb A e z ∈ A := (e.symm (Multiplicative.ofAdd z)).2

theorem emb_injective : Function.Injective (emb A e) := fun z w h =>
  Multiplicative.ofAdd.injective (e.symm.injective (Subtype.ext h))

end Emb

section Conj

variable {G : Type*} [Group G] {r : ℕ} {A : Subgroup G}
  {e : A ≃* Multiplicative (Fin r → ℤ)} {g : G} {T : Matrix (Fin r) (Fin r) ℤ}
  (hT : ∀ z : Fin r → ℤ, g * emb A e z * g⁻¹ = emb A e (T *ᵥ z))

include hT

end Conj

/-! ### Rosenblatt's polynomials: coefficients `0` or `1`, no constant term -/

/-! ### Lemma 4.15 for integer matrices and integer polynomials

The group computation happens over `ℤ` while the eigenvalue lives in `ℂ`, so Lemma 4.15 is
needed in the mixed form: an integer polynomial killing a basis vector under an integer matrix
vanishes at the complex eigenvalue.
-/

/-! ### Rosenblatt's set, and Theorem 4.17 when the eigenvalue is large -/

section Main

variable {G : Type*} [Group G] {r : ℕ} {A : Subgroup G}
  {e : A ≃* Multiplicative (Fin r → ℤ)}

theorem emb_add (z w : Fin r → ℤ) : emb A e (z + w) = emb A e z * emb A e w := by
  show ((e.symm (Multiplicative.ofAdd (z + w)) : A) : G) = _
  rw [show Multiplicative.ofAdd (z + w)
      = Multiplicative.ofAdd z * Multiplicative.ofAdd w from rfl, map_mul]
  rfl

variable (A e) (g : G) (T : Matrix (Fin r) (Fin r) ℤ)

end Main

section Main2

variable {G : Type*} [Group G] {r : ℕ} {A : Subgroup G}
  {e : A ≃* Multiplicative (Fin r → ℤ)} {g : G} {T : Matrix (Fin r) (Fin r) ℤ}
  (hT : ∀ z : Fin r → ℤ, g * emb A e z * g⁻¹ = emb A e (T *ᵥ z))

include hT

end Main2

section Final

variable {G : Type*} [Group G] {r : ℕ} {A : Subgroup G}
  {e : A ≃* Multiplicative (Fin r → ℤ)} {g : G} {T : Matrix (Fin r) (Fin r) ℤ}
  (hT : ∀ z : Fin r → ℤ, g * emb A e z * g⁻¹ = emb A e (T *ᵥ z))

include hT

end Final

/-! ### The `‖φ‖ < 1` case: passing to `g⁻¹`

This is where normality of `A` is needed.  Conjugation by `g⁻¹` also preserves `A`, so it too
is given by an integer matrix, and that matrix is a two-sided inverse of `T`.
-/

section Inverse

variable {G : Type*} [Group G] {r : ℕ} {A : Subgroup G} [hA : A.Normal]
  {e : A ≃* Multiplicative (Fin r → ℤ)} {g : G} {T : Matrix (Fin r) (Fin r) ℤ}

/-- Coordinates of an element of `A`. -/
def embInv (A : Subgroup G) (e : A ≃* Multiplicative (Fin r → ℤ)) (x : A) : Fin r → ℤ :=
  Multiplicative.toAdd (e x)

theorem emb_embInv (x : A) : emb A e (embInv A e x) = (x : G) := by
  show ((e.symm (Multiplicative.ofAdd (Multiplicative.toAdd (e x))) : A) : G) = (x : G)
  rw [show Multiplicative.ofAdd (Multiplicative.toAdd (e x)) = e x from rfl,
    MulEquiv.symm_apply_apply]

/-- Conjugation by `g⁻¹`, in coordinates.  Well defined because `A` is normal. -/
def conjInv (A : Subgroup G) [A.Normal] (e : A ≃* Multiplicative (Fin r → ℤ)) (g : G)
    (z : Fin r → ℤ) : Fin r → ℤ :=
  embInv A e ⟨g⁻¹ * emb A e z * g, by
    simpa using ‹A.Normal›.conj_mem _ (emb_mem A e z) g⁻¹⟩

theorem emb_conjInv (z : Fin r → ℤ) :
    emb A e (conjInv A e g z) = g⁻¹ * emb A e z * g := by
  rw [conjInv, emb_embInv]

theorem conjInv_add (z w : Fin r → ℤ) :
    conjInv A e g (z + w) = conjInv A e g z + conjInv A e g w := by
  refine emb_injective A e ?_
  rw [emb_add, emb_conjInv, emb_conjInv, emb_conjInv, emb_add]
  group

/-- The matrix of conjugation by `g⁻¹`. -/
def invMatrix (A : Subgroup G) [A.Normal] (e : A ≃* Multiplicative (Fin r → ℤ)) (g : G) :
    Matrix (Fin r) (Fin r) ℤ :=
  LinearMap.toMatrix' (AddMonoidHom.mk' (conjInv A e g) (conjInv_add)).toIntLinearMap

theorem invMatrix_mulVec (z : Fin r → ℤ) :
    (invMatrix A e g) *ᵥ z = conjInv A e g z := by
  rw [← Matrix.toLin'_apply, invMatrix, Matrix.toLin'_toMatrix']
  rfl

/-- Conjugation by `g⁻¹` satisfies the same hypothesis, with the inverse matrix. -/
theorem hT_inv (z : Fin r → ℤ) :
    g⁻¹ * emb A e z * (g⁻¹)⁻¹ = emb A e ((invMatrix A e g) *ᵥ z) := by
  rw [invMatrix_mulVec, emb_conjInv, inv_inv]

variable (hT : ∀ z : Fin r → ℤ, g * emb A e z * g⁻¹ = emb A e (T *ᵥ z))

include hT

end Inverse

section Final2

variable {G : Type*} [Group G] {r : ℕ} {A : Subgroup G} [A.Normal]
  {e : A ≃* Multiplicative (Fin r → ℤ)} {g : G} {T : Matrix (Fin r) (Fin r) ℤ}
  (hT : ∀ z : Fin r → ℤ, g * emb A e z * g⁻¹ = emb A e (T *ᵥ z))

include hT

end Final2

end Rosenblatt

/-!
# A subgroup of a polycyclic group is polycyclic

Rosenblatt uses this silently throughout §4 ("Since `G` is polycyclic, `T` is a finite normal
subgroup of `G`"), and it is what makes the terms of the derived series finitely generated, so
it is needed before the reduction of Theorem 4.12 can start.  It is absent from the polycyclic
library built for the Milnor and Wolf missions, which has the extension, quotient and cyclic
cases but not the subgroup case.

Given a normal series `⊤ = A₀ ⊇ A₁ ⊇ ⋯ ⊇ A_t = ⊥` of `G` with cyclic quotients and a subgroup
`L ≤ G`, intersecting the series with `L` gives a normal series of `L`, because

* `(A_{i+1} ∩ L)` is normal in `(A_i ∩ L)` — conjugation by an element of `A_i ∩ L` preserves
  `A_{i+1}` and preserves `L`; and
* `(A_i ∩ L)/(A_{i+1} ∩ L)` **injects** into `A_i/A_{i+1}`, so it is cyclic.

The library's existing `IsCyclicStep.subgroupOf` restricts a step to a subgroup *containing* it,
where the quotient map is surjective.  Here `L` is arbitrary and the quotient map is instead
injective, which is why a separate lemma is needed.
-/

namespace Rosenblatt

open MilnorWolf MilnorWolf.Lib

/-- A group admitting an injective homomorphism into a cyclic group is cyclic. -/
theorem isCyclic_of_injective {A B : Type*} [Group A] [Group B] [IsCyclic B]
    (f : A →* B) (hf : Function.Injective f) : IsCyclic A :=
  isCyclic_of_surjective (MonoidHom.ofInjective hf).symm (MulEquiv.surjective _)

/-- The inclusion of `K ∩ L`, viewed inside `L`, into `K`. -/
def inclKL {G : Type*} [Group G] (K L : Subgroup G) : ↥(K.subgroupOf L) →* ↥K :=
  (L.subtype.comp (K.subgroupOf L).subtype).codRestrict K
    fun x => Subgroup.mem_subgroupOf.1 x.2

@[simp] theorem inclKL_apply_coe {G : Type*} [Group G] (K L : Subgroup G)
    (x : ↥(K.subgroupOf L)) : ((inclKL K L x : ↥K) : G) = ((x : ↥L) : G) := rfl

/-- Intersecting one step of a normal series with an arbitrary subgroup `L` again gives a step:
the quotient injects into the original quotient, so it stays cyclic. -/
theorem isCyclicStep_subgroupOf {G : Type*} [Group G] {H K : Subgroup G}
    (h : IsCyclicStep H K) (L : Subgroup G) :
    IsCyclicStep (H.subgroupOf L) (K.subgroupOf L) := by
  obtain ⟨hle, hnorm, hcyc⟩ := h
  have hkey : (H.subgroupOf L).subgroupOf (K.subgroupOf L)
      = (H.subgroupOf K).comap (inclKL K L) := by
    ext x
    simp [Subgroup.mem_subgroupOf, Subgroup.mem_comap]
  refine ⟨Subgroup.comap_mono hle, ?_⟩
  have hn : ((H.subgroupOf K).comap (inclKL K L)).Normal := hnorm.comap _
  rw [hkey]
  refine ⟨hn, ?_⟩
  -- the induced map on quotients is injective
  refine isCyclic_of_injective
    (QuotientGroup.lift ((H.subgroupOf K).comap (inclKL K L))
      ((QuotientGroup.mk' (H.subgroupOf K)).comp (inclKL K L))
      (fun x hx => (QuotientGroup.eq_one_iff _).2 hx)) ?_
  intro a b hab
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
  have hx : (QuotientGroup.mk' (H.subgroupOf K)) (inclKL K L x)
      = (QuotientGroup.mk' (H.subgroupOf K)) (inclKL K L y) := hab
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hx
  rw [QuotientGroup.eq]
  simpa [Subgroup.mem_comap, map_mul, map_inv] using hx

/-- A subgroup of a polycyclic group is polycyclic. -/
theorem isPolycyclic_subgroup {G : Type*} [Group G] (h : IsPolycyclic G) (L : Subgroup G) :
    IsPolycyclic L := by
  obtain ⟨A, h0, ⟨t, ht⟩, hstep⟩ := exists_chain_of_isPolycyclic h
  refine isPolycyclic_of_chain (A := fun n => (A n).subgroupOf L) ⟨?_, ⟨t, ?_⟩, ?_⟩
  · show (A 0).subgroupOf L = ⊤
    rw [h0, Subgroup.top_subgroupOf]
  · show (A t).subgroupOf L = ⊥
    rw [ht, Subgroup.bot_subgroupOf]
  · exact fun i => isCyclicStep_subgroupOf (hstep i) L

/-! ### The torsion subgroup of an abelian subgroup -/

/-- The torsion subgroup of an abelian subgroup `A`, as a subgroup of the ambient group.
Commutativity of `A` is what makes the set of its elements of finite order closed under
multiplication. -/
def torsionSub {G : Type*} [Group G] (A : Subgroup G)
    (hab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) : Subgroup G where
  carrier := {g | g ∈ A ∧ IsOfFinOrder g}
  one_mem' := ⟨A.one_mem, IsOfFinOrder.one⟩
  mul_mem' := by
    rintro x y ⟨hxA, hx⟩ ⟨hyA, hy⟩
    refine ⟨A.mul_mem hxA hyA, ?_⟩
    obtain ⟨m, hm, hxm⟩ := isOfFinOrder_iff_pow_eq_one.1 hx
    obtain ⟨n, hn, hyn⟩ := isOfFinOrder_iff_pow_eq_one.1 hy
    refine isOfFinOrder_iff_pow_eq_one.2 ⟨m * n, by positivity, ?_⟩
    have hc : Commute x y := hab x hxA y hyA
    rw [hc.mul_pow, pow_mul, hxm, one_pow, mul_comm m n, pow_mul, hyn, one_pow, mul_one]
  inv_mem' := by
    rintro x ⟨hxA, hx⟩
    exact ⟨A.inv_mem hxA, hx.inv⟩

@[simp] theorem mem_torsionSub {G : Type*} [Group G] {A : Subgroup G}
    {hab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x} {g : G} :
    g ∈ torsionSub A hab ↔ g ∈ A ∧ IsOfFinOrder g := Iff.rfl

/-! ### The quotient by the torsion subgroup is torsion-free -/

/-! ### Quotients, and finite index through a subgroup -/

end Rosenblatt

/-!
# Rosenblatt 4.12's core step, reduced to Theorem 4.17 and the linear-algebra leaf

The core step is: a polycyclic group with no free subsemigroup of rank two, having a normal
abelian torsion-free subgroup `A` with nilpotent quotient, is almost nilpotent.

This file supplies the three things that stand between the core step's hypotheses and the
linear-algebra leaf, and then composes them.

1. **`A ≅ ℤ^k`.**  `A` is finitely generated, being a subgroup of a polycyclic group; with
   abelian and torsion-free that makes `Additive A` a finitely generated torsion-free
   `ℤ`-module, hence free of finite rank by Mathlib's `Module.basisOfFiniteTypeTorsionFree'`.
2. **The matrix of conjugation by each `g`.**  Already available: `invMatrix A e g` is the
   matrix of conjugation by `g⁻¹`, so `invMatrix A e g⁻¹` is the matrix of conjugation by `g`.
3. **Every eigenvalue lies on the unit circle.**  This is Theorem 4.17 in contrapositive form:
   an eigenvalue off the unit circle would produce a free subsemigroup.

The leaf then finishes it.  Here the leaf is taken as a hypothesis, so that the composition can
be checked before it is published; the submitted version imports it.
-/

namespace Rosenblatt

open scoped Matrix

/-- Transport a multiplicative group across the additive coordinates of a basis. -/
noncomputable def mulEquivOfAddEquiv {M : Type*} [CommGroup M] {k : ℕ}
    (L : Additive M ≃+ (Fin k → ℤ)) : M ≃* Multiplicative (Fin k → ℤ) where
  toFun x := Multiplicative.ofAdd (L (Additive.ofMul x))
  invFun y := Additive.toMul (L.symm (Multiplicative.toAdd y))
  left_inv x := by simp
  right_inv y := by simp
  map_mul' x y := by
    show Multiplicative.ofAdd (L (Additive.ofMul (x * y)))
        = Multiplicative.ofAdd (L (Additive.ofMul x)) *
          Multiplicative.ofAdd (L (Additive.ofMul y))
    rw [show Additive.ofMul (x * y) = Additive.ofMul x + Additive.ofMul y from rfl, map_add]
    rfl

/-- **Step 1**: a finitely generated abelian torsion-free group is free abelian of finite rank. -/
theorem exists_mulEquiv_pi_int {M : Type*} [Group M] [Group.FG M]
    (hab : ∀ x y : M, x * y = y * x) (htf : IsMulTorsionFree M) :
    ∃ k : ℕ, Nonempty (M ≃* Multiplicative (Fin k → ℤ)) := by
  letI : CommGroup M := ⟨hab⟩
  have hfg : AddGroup.FG (Additive M) := by infer_instance
  have hfin : Module.Finite ℤ (Additive M) := Module.Finite.iff_addGroup_fg.mpr hfg
  have htf2 : IsAddTorsionFree (Additive M) := by infer_instance
  obtain ⟨k, b⟩ := Module.basisOfFiniteTypeTorsionFree' (R := ℤ) (M := Additive M)
  exact ⟨k, ⟨mulEquivOfAddEquiv b.equivFun.toAddEquiv⟩⟩

section Core

variable {G : Type*} [Group G] {k : ℕ} {A : Subgroup G} [A.Normal]
  (e : A ≃* Multiplicative (Fin k → ℤ))

/-- **Step 2**: the matrix of conjugation by `g`, read off the matrix of conjugation by `g⁻¹`. -/
theorem conj_matrix_spec (g : G) (z : Fin k → ℤ) :
    g * emb A e z * g⁻¹ = emb A e ((invMatrix A e g⁻¹) *ᵥ z) := by
  have h := hT_inv (A := A) (e := e) (g := g⁻¹) z
  rwa [inv_inv] at h

end Core

section Compose

variable {G : Type*} [Group G]

end Compose

end Rosenblatt

/-!
# Rosenblatt 4.12's core step, reduced to Theorem 4.17 and the linear-algebra leaf

The submitted form of `R_red_core.lean`: the two inputs are the **published** statements rather
than hypotheses, so the reduction is recorded on the platform as depending on them.

* Theorem 4.17 — `Rosenblatt.hasFreeSubsemigroupOfRankTwo_of_exists_eigenvalue_norm_ne_one`,
  proved.
* The linear-algebra half — `Rosenblatt.isVirtuallyNilpotent_of_isPolycyclic_of_isNilpotent_quotient_of_forall_eigenvalue_norm_eq_one`,
  open, and itself reducible to Kronecker (in Mathlib) and Mal'cev's theorem (published here as
  an external).

The three steps in between are proved in `R_red_core.lean` and reused.
-/

namespace Rosenblatt

open scoped Matrix

/-- **Rosenblatt 4.12's core step**, reduced to Theorem 4.17 and the linear-algebra half. -/
theorem core_step_sub {G : Type*} [Group G] (hpoly : MilnorWolf.IsPolycyclic G)
    (hfree : ¬ Chou.HasFreeSubsemigroupOfRankTwo G)
    (A : Subgroup G) [A.Normal] (hab : ∀ x y : A, x * y = y * x)
    (htf : IsMulTorsionFree A) (hnil : Group.IsNilpotent (G ⧸ A)) :
    Group.IsVirtuallyNilpotent G := by
  -- Step 1: `A` is free abelian of finite rank
  have hfgA : Group.FG A := MilnorWolf.Lib.fg_of_isPolycyclic (isPolycyclic_subgroup hpoly A)
  haveI := hfgA
  obtain ⟨k, ⟨e⟩⟩ := exists_mulEquiv_pi_int (M := A) hab htf
  -- Step 2 and the hand-off to the linear-algebra half
  refine isVirtuallyNilpotent_of_isPolycyclic_of_isNilpotent_quotient_of_forall_eigenvalue_norm_eq_one
    hpoly A e (fun g => invMatrix A e g⁻¹) (fun g z => conj_matrix_spec e g z) hnil ?_
  -- Step 3: Theorem 4.17 in contrapositive form
  intro g φ v hv hev
  by_contra hne
  exact hfree
    (hasFreeSubsemigroupOfRankTwo_of_exists_eigenvalue_norm_ne_one A e g
      (invMatrix A e g⁻¹) (fun z => conj_matrix_spec e g z) φ v hv hev hne)

end Rosenblatt

theorem solution {G : Type*} [Group G] (hpoly : MilnorWolf.IsPolycyclic G)
    (hfree : ¬ Chou.HasFreeSubsemigroupOfRankTwo G)
    (A : Subgroup G) [A.Normal] (hab : ∀ x y : A, x * y = y * x)
    (htf : IsMulTorsionFree A) (hnil : Group.IsNilpotent (G ⧸ A)) :
    Group.IsVirtuallyNilpotent G :=
  Rosenblatt.core_step_sub hpoly hfree A hab htf hnil
