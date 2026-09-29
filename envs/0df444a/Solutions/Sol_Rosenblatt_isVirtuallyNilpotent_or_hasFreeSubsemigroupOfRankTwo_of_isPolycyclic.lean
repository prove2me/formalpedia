-- Prove2me | solution 1 for Rosenblatt.isVirtuallyNilpotent_or_hasFreeSubsemigroupOfRankTwo_of_isPolycyclic
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-24T19:29:29.580985+00:00
-- url     : https://prove2.me/submissions/25ed9e99-55ad-41ea-bc47-f7e1e76a21a1

import Theorems.Thm_GroupFiniteness_fg_of_extension
import Definitions.Def_MilnorWolf_Growth
import Mathlib
import Definitions.Def_Chou_Growth
import Theorems.Thm_Rosenblatt_isVirtuallyNilpotent_of_isPolycyclic_of_abelian_isMulTorsionFree_isNilpotent_quotient_of_not_hasFreeSubsemigroupOfRankTwo

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
# Rosenblatt, Theorem 4.7 (p. 41)

*Invariant measures and growth conditions*, Trans. Amer. Math. Soc. 193 (1974).

A finitely generated solvable group with no free subsemigroup on two generators is polycyclic.

The proof is the induction along the derived series that Rosenblatt runs on p. 41.  Write
`G⁽ⁿ⁾` for the `n`-th derived subgroup and induct on an `n` with `G⁽ⁿ⁾ = 1`, which exists
because `G` is solvable.

* `n = 0` makes `G` trivial.
* For `n + 1`, put `N = G⁽ⁿ⁾`.  It is abelian, since `⁅N, N⁆ = G⁽ⁿ⁺¹⁾ = 1`.  The quotient
  `G/N` is again finitely generated with no free subsemigroup (the property passes to
  quotients, `Chou.not_hasFreeSubsemigroupOfRankTwo_quotient`) and satisfies
  `(G/N)⁽ⁿ⁾ = 1`, so the inductive hypothesis makes it polycyclic.  Rosenblatt's Lemma 4.9 —
  published here as
  `Chou.fg_of_isVirtuallyPolycyclic_quotient_of_not_hasFreeSubsemigroupOfRankTwo` — then makes
  `N` finitely generated, hence polycyclic as a finitely generated abelian group, and `G` is
  polycyclic as an extension.

The abelian hypothesis on `N` is what pins the induction to the *derived* series rather than
any normal series: it is exactly what makes a finitely generated `N` polycyclic.
-/


namespace Rosenblatt

open Chou MilnorWolf
open scoped commutatorElement

/-- A free subsemigroup of rank two in a quotient lifts to one in the group: choose preimages
of the two elements, and the word map on them composes with the projection to give the word map
downstairs, so injectivity downstairs forces injectivity upstairs.

Proved in `Chou.Lib` in this repository as `hasFreeSubsemigroupOfRankTwo_of_quotient`, and
repeated here so that this solution imports no `Open` theorem. -/
theorem hasFreeSubsemigroupOfRankTwo_of_quotient {G : Type*} [Group G] (N : Subgroup G)
    [N.Normal] (h : HasFreeSubsemigroupOfRankTwo (G ⧸ N)) : HasFreeSubsemigroupOfRankTwo G := by
  obtain ⟨a, b, hab⟩ := h
  obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
  refine ⟨a', b', ?_⟩
  have key : (FreeMonoid.lift ![(a' : G ⧸ N), (b' : G ⧸ N)] : FreeMonoid (Fin 2) →* G ⧸ N)
      = (QuotientGroup.mk' N).comp (FreeMonoid.lift ![a', b']) := by
    refine FreeMonoid.hom_eq fun x => ?_
    fin_cases x <;> simp
  rw [key, MonoidHom.coe_comp] at hab
  exact hab.of_comp

/-- Contrapositive of `hasFreeSubsemigroupOfRankTwo_of_quotient`. -/
theorem not_hasFreeSubsemigroupOfRankTwo_quotient {G : Type*} [Group G] (N : Subgroup G)
    [N.Normal] (h : ¬ HasFreeSubsemigroupOfRankTwo G) :
    ¬ HasFreeSubsemigroupOfRankTwo (G ⧸ N) :=
  fun hq => h (hasFreeSubsemigroupOfRankTwo_of_quotient N hq)

/-- The `n`-th derived subgroup is abelian as soon as the `(n+1)`-st is trivial. -/
theorem mul_comm_derivedSeries {G : Type*} [Group G] {n : ℕ}
    (h : derivedSeries G (n + 1) = ⊥) (x y : derivedSeries G n) : x * y = y * x := by
  have hmem : ⁅(x : G), (y : G)⁆ ∈ derivedSeries G (n + 1) := by
    rw [derivedSeries_succ]
    exact Subgroup.commutator_mem_commutator x.2 y.2
  rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
  exact Subtype.ext (by simpa using hmem)

/-- The quotient by the `n`-th derived subgroup has trivial `n`-th derived subgroup. -/
theorem derivedSeries_quotient_eq_bot {G : Type*} [Group G] (n : ℕ) :
    derivedSeries (G ⧸ derivedSeries G n) n = ⊥ := by
  have : (derivedSeries G n).Normal := derivedSeries_normal G n
  rw [← map_derivedSeries_eq (f := QuotientGroup.mk' (derivedSeries G n))
      (QuotientGroup.mk'_surjective _) n,
    Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']

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

theorem torsionSub_le {G : Type*} [Group G] (A : Subgroup G)
    (hab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) : torsionSub A hab ≤ A :=
  fun _ h => h.1

/-- The torsion subgroup of a normal abelian subgroup is normal in the ambient group:
conjugation preserves `A` and preserves the order of an element. -/
theorem torsionSub_normal {G : Type*} [Group G] (A : Subgroup G) [hA : A.Normal]
    (hab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) : (torsionSub A hab).Normal := by
  refine ⟨fun t ht g => ⟨hA.conj_mem t ht.1 g, ?_⟩⟩
  obtain ⟨n, hn, htn⟩ := isOfFinOrder_iff_pow_eq_one.1 ht.2
  refine isOfFinOrder_iff_pow_eq_one.2 ⟨n, hn, ?_⟩
  rw [conj_pow, htn, mul_one, mul_inv_cancel]

/-- The torsion subgroup of an abelian subgroup of a polycyclic group is finite: it is finitely
generated, being a subgroup of a polycyclic group, and a finitely generated abelian torsion
group is finite. -/
theorem finite_torsionSub {G : Type*} [Group G] (hpoly : IsPolycyclic G) (A : Subgroup G)
    (hab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) : Finite (torsionSub A hab) := by
  have hfg : Group.FG (torsionSub A hab) :=
    Lib.fg_of_isPolycyclic (isPolycyclic_subgroup hpoly (torsionSub A hab))
  letI : CommGroup (torsionSub A hab) :=
    ⟨fun x y => Subtype.ext (hab x (torsionSub_le A hab x.2) y (torsionSub_le A hab y.2))⟩
  haveI := hfg
  refine CommGroup.finite_of_fg_isMulTorsion _ (fun x => ?_)
  obtain ⟨n, hn, hxn⟩ := isOfFinOrder_iff_pow_eq_one.1 x.2.2
  exact isOfFinOrder_iff_pow_eq_one.2 ⟨n, hn, Subtype.ext (by simpa using hxn)⟩

/-! ### The quotient by the torsion subgroup is torsion-free -/

/-- In an abelian group, Mathlib's power-injectivity form of torsion-freeness follows from the
absence of nontrivial elements of finite order.  The two are *not* equivalent without
commutativity, which is why `hab` appears. -/
theorem isMulTorsionFree_of_comm {H : Type*} [Group H] (hab : ∀ x y : H, x * y = y * x)
    (h : ∀ x : H, IsOfFinOrder x → x = 1) : IsMulTorsionFree H := by
  refine ⟨fun {n} hn a b heq0 => ?_⟩
  have heq : a ^ n = b ^ n := heq0
  have hc : Commute a b⁻¹ := hab a b⁻¹
  have hone : (a * b⁻¹) ^ n = 1 := by
    rw [hc.mul_pow, inv_pow, heq, mul_inv_cancel]
  have := h _ (isOfFinOrder_iff_pow_eq_one.2 ⟨n, Nat.pos_of_ne_zero hn, hone⟩)
  exact mul_inv_eq_one.mp this

/-- The image of `A` in the quotient by its torsion subgroup is torsion-free: if a power of the
class of `a` is trivial then that power of `a` is itself of finite order, so `a` is too, so `a`
already lies in the torsion subgroup. -/
theorem isMulTorsionFree_map_torsionSub {G : Type*} [Group G] (A : Subgroup G)
    (hab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) [(torsionSub A hab).Normal] :
    IsMulTorsionFree (A.map (QuotientGroup.mk' (torsionSub A hab))) := by
  refine isMulTorsionFree_of_comm (fun x y => ?_) (fun x hx => ?_)
  · obtain ⟨a, haA, hax⟩ := x.2
    obtain ⟨b, hbA, hbx⟩ := y.2
    refine Subtype.ext ?_
    simp only [Subgroup.coe_mul]
    rw [← hax, ← hbx, ← map_mul, ← map_mul, hab a haA b hbA]
  · obtain ⟨a, haA, hax⟩ := x.2
    obtain ⟨n, hn, hxn⟩ := isOfFinOrder_iff_pow_eq_one.1 hx
    have hmem : a ^ n ∈ torsionSub A hab := by
      have h1 := congrArg (Subtype.val) hxn
      rw [Subgroup.coe_pow, Subgroup.coe_one, ← hax, ← map_pow] at h1
      exact (QuotientGroup.eq_one_iff _).1 h1
    obtain ⟨m, hm, ham⟩ := isOfFinOrder_iff_pow_eq_one.1 hmem.2
    have hfin : IsOfFinOrder a :=
      isOfFinOrder_iff_pow_eq_one.2 ⟨n * m, by positivity, by rw [pow_mul, ham]⟩
    refine Subtype.ext ?_
    rw [← hax]
    exact (QuotientGroup.eq_one_iff _).2 ⟨haA, hfin⟩

/-! ### Quotients, and finite index through a subgroup -/

/-- Mapping one step of a normal series along **any** homomorphism again gives a step: the new
quotient is a quotient of the old one, so it stays cyclic.  Surjectivity of `f` is not needed —
the restriction of `f` to `K` is surjective onto `K.map f` by construction. -/
theorem isCyclicStep_map {G Q : Type*} [Group G] [Group Q] {H K : Subgroup G}
    (h : IsCyclicStep H K) (f : G →* Q) : IsCyclicStep (H.map f) (K.map f) := by
  obtain ⟨hle, hnorm, hcyc⟩ := h
  -- the restriction of `f` to `K`, onto `K.map f`
  set φ : ↥K →* ↥(K.map f) :=
    ((f.comp K.subtype).codRestrict (K.map f) fun x => ⟨x, x.2, rfl⟩) with hφ
  have hφsurj : Function.Surjective φ := by
    rintro ⟨y, x, hxK, rfl⟩
    exact ⟨⟨x, hxK⟩, rfl⟩
  have hkey : (H.map f).subgroupOf (K.map f) = (H.subgroupOf K).map φ := by
    ext y
    constructor
    · rintro hy
      obtain ⟨a, haH, hay⟩ := Subgroup.mem_subgroupOf.1 hy
      exact ⟨⟨a, hle haH⟩, Subgroup.mem_subgroupOf.2 haH, Subtype.ext hay⟩
    · rintro ⟨x, hx, rfl⟩
      exact Subgroup.mem_subgroupOf.2 ⟨(x : G), Subgroup.mem_subgroupOf.1 hx, rfl⟩
  refine ⟨Subgroup.map_mono hle, ?_⟩
  rw [hkey]
  have hn : ((H.subgroupOf K).map φ).Normal := hnorm.map φ hφsurj
  refine ⟨hn, ?_⟩
  -- the quotient downstairs is a quotient of the cyclic quotient upstairs
  refine isCyclic_of_surjective
    (QuotientGroup.lift (H.subgroupOf K)
      ((QuotientGroup.mk' ((H.subgroupOf K).map φ)).comp φ)
      (fun x hx => (QuotientGroup.eq_one_iff _).2 ⟨x, hx, rfl⟩)) ?_
  intro y
  obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective y
  obtain ⟨x, rfl⟩ := hφsurj z
  exact ⟨QuotientGroup.mk x, rfl⟩

/-- A quotient of a polycyclic group is polycyclic. -/
theorem isPolycyclic_of_surjective {G Q : Type*} [Group G] [Group Q] (h : IsPolycyclic G)
    (f : G →* Q) (hf : Function.Surjective f) : IsPolycyclic Q := by
  obtain ⟨A, h0, ⟨t, ht⟩, hstep⟩ := exists_chain_of_isPolycyclic h
  refine isPolycyclic_of_chain (A := fun n => (A n).map f) ⟨?_, ⟨t, ?_⟩, ?_⟩
  · show (A 0).map f = ⊤
    rw [h0]
    exact Subgroup.map_top_of_surjective f hf
  · show (A t).map f = ⊥
    rw [ht]
    simp
  · exact fun i => isCyclicStep_map (hstep i) f

/-- Finite index composes along the inclusion of a subgroup: a finite-index subgroup of a
finite-index subgroup has finite index in the whole group. -/
theorem finiteIndex_map_subtype {G : Type*} [Group G] (K : Subgroup G) [K.FiniteIndex]
    (H : Subgroup K) [H.FiniteIndex] : (H.map K.subtype).FiniteIndex := by
  refine ⟨?_⟩
  rw [Subgroup.index_map, K.ker_subtype, sup_bot_eq, K.range_subtype]
  exact Nat.mul_ne_zero Subgroup.FiniteIndex.index_ne_zero Subgroup.FiniteIndex.index_ne_zero

end Rosenblatt

/-!
# Rosenblatt Theorem 4.12: the reduction to the `ℤ^k`-by-nilpotent case

Rosenblatt's proof of Theorem 4.12 (pp. 48–49) has two halves.  The second half is the
substantial one — it is about `GL_k(ℤ)`, eigenvalues on and off the unit circle, Kronecker's
theorem and a simultaneous triangularization — and it is published separately as the statement
`Rosenblatt.isVirtuallyNilpotent_of_isPolycyclic_of_isNilpotent_quotient_of_not_hasFreeSubsemigroupOfRankTwo`.

This file is the first half: the purely group-theoretic reduction of Theorem 4.12 to that
statement.  Two moves make it up.

* **Torsion removal.** The last nontrivial term `A` of the derived series is abelian, so its
  torsion subgroup `T` is finite and normal in the whole group, and one may pass to `G/T`, in
  which the corresponding term is torsion-free.  Getting back down is Rosenblatt's centralizer
  argument: a nilpotent subgroup `N` of finite index in `G/T` pulls back to `K` of finite index
  in `G`, and the centralizer of `T` in `K` is still of finite index (because `T` is finite) and
  is nilpotent (because `T` lands in its centre and the quotient by `T` is nilpotent).

* **Induction down the derived series.** With the term torsion-free, `G/A` has a shorter derived
  series, so by induction it has a nilpotent subgroup `M` of finite index; the preimage `K` of
  `M` is of finite index in `G` with `K/A` nilpotent and `A` a normal, abelian, torsion-free
  subgroup of `K`.  That is exactly the published statement's hypothesis.

Rosenblatt writes the torsion removal as a "without loss of generality".  It cannot be one here:
taken literally it is a second induction, so it is done uniformly instead — every group is
pushed through `G/T`, with the torsion-free case isolated as its own lemma.
-/


namespace Rosenblatt

open Chou MilnorWolf
open scoped commutatorElement

/-! ### The centralizer of a finite normal subgroup has finite index -/

/-- Conjugation by `g` as a permutation of a normal subgroup `T`. -/
def conjPerm {G : Type*} [Group G] (T : Subgroup G) [hT : T.Normal] (g : G) : Equiv.Perm T where
  toFun t := ⟨g * t * g⁻¹, hT.conj_mem t t.2 g⟩
  invFun t := ⟨g⁻¹ * t * g, by simpa using hT.conj_mem t t.2 g⁻¹⟩
  left_inv t := by ext; simp [mul_assoc]
  right_inv t := by ext; simp [mul_assoc]

/-- The conjugation action of `G` on a normal subgroup `T`, as a homomorphism to the permutation
group of `T`. -/
def conjHom {G : Type*} [Group G] (T : Subgroup G) [T.Normal] : G →* Equiv.Perm T :=
  MonoidHom.mk' (fun g => conjPerm T g) <| by
    intro a b
    ext t
    simp [conjPerm, mul_assoc]

@[simp] theorem conjHom_apply_coe {G : Type*} [Group G] (T : Subgroup G) [T.Normal] (g : G)
    (t : T) : ((conjHom T g) t : G) = g * (t : G) * g⁻¹ := rfl

theorem ker_conjHom {G : Type*} [Group G] (T : Subgroup G) [T.Normal] :
    (conjHom T).ker = Subgroup.centralizer (T : Set G) := by
  ext g
  simp only [MonoidHom.mem_ker, Subgroup.mem_centralizer_iff]
  constructor
  · intro h t ht
    have key : g * t * g⁻¹ = t := by
      have := congrArg (fun e => ((e : Equiv.Perm T) ⟨t, ht⟩ : G)) h
      simpa using this
    calc t * g = (g * t * g⁻¹) * g := by rw [key]
      _ = g * t := by group
  · intro h
    refine Equiv.ext fun t => Subtype.ext ?_
    have ht := h (t : G) t.2
    show g * (t : G) * g⁻¹ = (t : G)
    rw [← ht]
    group

/-- The centralizer of a finite normal subgroup has finite index: the group acts on the finite
set `T` by conjugation, and the kernel of that action is the centralizer. -/
theorem finiteIndex_centralizer_of_finite {G : Type*} [Group G] (T : Subgroup G) [T.Normal]
    [Finite T] : (Subgroup.centralizer (T : Set G)).FiniteIndex := by
  rw [← ker_conjHom T]
  exact Subgroup.finiteIndex_ker (conjHom T)

/-! ### Rosenblatt's centralizer argument: removing a finite abelian normal subgroup -/

/-- Rosenblatt, p. 48: if `T` is a finite abelian normal subgroup of `G` and `G/T` has a
nilpotent subgroup of finite index, then so does `G`.

Given a nilpotent `N` of finite index in `G/T`, its preimage `K` is of finite index in `G`, and
`H = K ⊓ C` — where `C` is the centralizer of `T` — is still of finite index, because `T` is
finite.  `H` is nilpotent: `T` lies in the centre of `H` by the definition of `C`, and `H/T`
embeds in `N`, so `H/Z(H)` is a quotient of a nilpotent group. -/
theorem isVirtuallyNilpotent_of_finite_abelian_normal_quotient {G : Type*} [Group G]
    (T : Subgroup G) [T.Normal] [Finite T]
    (hab : ∀ x ∈ T, ∀ y ∈ T, x * y = y * x)
    (h : Group.IsVirtuallyNilpotent (G ⧸ T)) : Group.IsVirtuallyNilpotent G := by
  obtain ⟨N, hNnil, hNfi⟩ := h
  have hCfi : (Subgroup.centralizer (T : Set G)).FiniteIndex :=
    finiteIndex_centralizer_of_finite T
  have hKfi : (N.comap (QuotientGroup.mk' T)).FiniteIndex := by
    refine ⟨?_⟩
    rw [Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective T)]
    exact hNfi.index_ne_zero
  set H := N.comap (QuotientGroup.mk' T) ⊓ Subgroup.centralizer (T : Set G) with hHdef
  have : H.FiniteIndex := by rw [hHdef]; infer_instance
  have hTH : T ≤ H := by
    refine le_inf (fun t ht => ?_) (fun t ht => ?_)
    · simpa [Subgroup.mem_comap, QuotientGroup.mk'_apply,
        (QuotientGroup.eq_one_iff t).2 ht] using N.one_mem
    · exact Subgroup.mem_centralizer_iff.2 fun x hx => hab x hx t ht
  set f : H →* G ⧸ T := (QuotientGroup.mk' T).comp H.subtype with hfdef
  have hker : f.ker = T.subgroupOf H := by
    ext x
    simp [hfdef, MonoidHom.mem_ker, Subgroup.mem_subgroupOf, QuotientGroup.eq_one_iff]
  have hrange : f.range ≤ N := by
    rintro _ ⟨x, rfl⟩
    exact (Subgroup.mem_inf.1 x.2).1
  have : (T.subgroupOf H).Normal := Subgroup.Normal.subgroupOf ‹T.Normal› H
  have hquotT : Group.IsNilpotent (H ⧸ T.subgroupOf H) := by
    have h1 : Group.IsNilpotent f.range :=
      Group.nilpotent_of_surjective
        (Subgroup.subgroupOfEquivOfLe hrange).toMonoidHom (MulEquiv.surjective _)
    have h2 : (H ⧸ f.ker) ≃* f.range := QuotientGroup.quotientKerEquivRange f
    have := h1
    exact Group.nilpotent_of_mulEquiv
      (h2.symm.trans (QuotientGroup.quotientMulEquivOfEq hker))
  have hcentral : T.subgroupOf H ≤ Subgroup.center H := by
    intro t ht
    rw [Subgroup.mem_center_iff]
    intro g
    refine Subtype.ext ?_
    have hg := Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 g.2).2
    exact (hg (t : G) (Subgroup.mem_subgroupOf.1 ht)).symm
  have hquotZ : Group.IsNilpotent (H ⧸ Subgroup.center H) := by
    haveI := hquotT
    refine Group.nilpotent_of_surjective
      (QuotientGroup.lift (T.subgroupOf H) (QuotientGroup.mk' (Subgroup.center H))
        (fun x hx => (QuotientGroup.eq_one_iff _).2 (hcentral hx))) ?_
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    exact ⟨QuotientGroup.mk x, rfl⟩
  exact ⟨H, Group.of_quotient_center_nilpotent hquotZ, inferInstance⟩

end Rosenblatt

/-!
# Rosenblatt Theorem 4.12: the induction

This is the assembly of the reduction begun in `R_red412.lean` and `R_polysub.lean`.  Induct on
an `n` with the `n`-th derived subgroup of `G` trivial, which exists because a polycyclic group
is solvable.

* `n = 0` makes `G` trivial.
* For `n + 1`, the last nontrivial derived term `A` is abelian.  Its torsion subgroup `T` is
  finite and normal in `G`, so by Rosenblatt's centralizer argument it is enough to handle
  `G/T` — where the corresponding term `A/T` is torsion-free.
* The torsion-free case is `isVirtuallyNilpotent_of_torsionFree`: `G/A` has a shorter derived
  series, so the inductive hypothesis gives it a nilpotent subgroup `M` of finite index; the
  preimage `K` of `M` is of finite index in `G`, is polycyclic, has no free subsemigroup, and
  has `A ∩ K` normal, abelian and torsion-free with nilpotent quotient `M`.  That is exactly
  the hypothesis of the published core step, which makes `K` almost nilpotent, and a nilpotent
  subgroup of finite index in `K` is one of finite index in `G`.
-/


namespace Rosenblatt

open Chou MilnorWolf MilnorWolf.Lib
open scoped commutatorElement

/-- Torsion-freeness transfers along an injective homomorphism. -/
theorem isMulTorsionFree_of_injective {A B : Type*} [Group A] [Group B] [IsMulTorsionFree B]
    (f : A →* B) (hf : Function.Injective f) : IsMulTorsionFree A := by
  refine ⟨fun {n} hn a b heq0 => ?_⟩
  have heq : a ^ n = b ^ n := heq0
  refine hf (IsMulTorsionFree.pow_left_injective hn ?_)
  simpa [← map_pow] using congrArg f heq

/-- The inclusion of `K ∩ L` into `K` is injective. -/
theorem inclKL_injective {G : Type*} [Group G] (K L : Subgroup G) :
    Function.Injective (inclKL K L) := by
  intro a b hab
  refine Subtype.ext (Subtype.ext ?_)
  simpa using congrArg (Subtype.val) hab

/-- A nilpotent subgroup of a subgroup, pushed into the ambient group, is still nilpotent. -/
theorem isNilpotent_map_subtype {G : Type*} [Group G] (K : Subgroup G) (H : Subgroup K)
    (h : Group.IsNilpotent H) : Group.IsNilpotent (H.map K.subtype) := by
  haveI := h
  exact Group.nilpotent_of_surjective
    (Subgroup.equivMapOfInjective H K.subtype (Subgroup.subtype_injective K)).toMonoidHom
    (MulEquiv.surjective _)

/-- A free subsemigroup of rank two in a subgroup gives one in the group.  Proved in `Chou.Rbt`
in this repository as `not_hasFreeSubsemigroupOfRankTwo_subgroup`, and repeated here because
that module's declarations share bare names with the polycyclic library and so cannot be merged
alongside it into one solution file. -/
theorem not_hasFreeSubsemigroupOfRankTwo_subgroup {G : Type*} [Group G]
    (h : ¬ HasFreeSubsemigroupOfRankTwo G) (H : Subgroup G) :
    ¬ HasFreeSubsemigroupOfRankTwo H := by
  rintro ⟨a, b, hinj⟩
  refine h ⟨(a : G), (b : G), ?_⟩
  have hcomp : FreeMonoid.lift ![(a : G), (b : G)]
      = (H.subtype).comp (FreeMonoid.lift ![a, b]) := by
    refine FreeMonoid.hom_eq ?_
    intro x
    fin_cases x <;> simp
  rw [hcomp, MonoidHom.coe_comp]
  exact (Subgroup.subtype_injective H).comp hinj

/-- The torsion-free case of the induction step: it is exactly the published core step, applied
to the preimage of a nilpotent subgroup of finite index in `G/A`. -/
theorem isVirtuallyNilpotent_of_torsionFree {n : ℕ} {G : Type u} [Group G]
    (ih : ∀ (Q : Type u) [Group Q], IsPolycyclic Q → ¬ HasFreeSubsemigroupOfRankTwo Q →
      derivedSeries Q n = ⊥ → Group.IsVirtuallyNilpotent Q)
    (hpoly : IsPolycyclic G) (hfree : ¬ HasFreeSubsemigroupOfRankTwo G)
    (hbot : derivedSeries G (n + 1) = ⊥)
    (htf : IsMulTorsionFree (derivedSeries G n)) :
    Group.IsVirtuallyNilpotent G := by
  have hAn : (derivedSeries G n).Normal := derivedSeries_normal G n
  -- the quotient by `A` satisfies the inductive hypothesis
  obtain ⟨M, hMnil, hMfi⟩ :=
    ih (G ⧸ derivedSeries G n)
      (isPolycyclic_of_surjective hpoly _ (QuotientGroup.mk'_surjective _))
      (not_hasFreeSubsemigroupOfRankTwo_quotient _ hfree)
      (derivedSeries_quotient_eq_bot n)
  set K := M.comap (QuotientGroup.mk' (derivedSeries G n)) with hK
  have hKfi : K.FiniteIndex := by
    refine ⟨?_⟩
    rw [hK, Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective _)]
    exact hMfi.index_ne_zero
  have hsub : ((derivedSeries G n).subgroupOf K).Normal := Subgroup.Normal.subgroupOf hAn K
  -- `A ∩ K` is abelian
  have habAK : ∀ x y : ((derivedSeries G n).subgroupOf K), x * y = y * x := by
    intro x y
    have hx : ((x : K) : G) ∈ derivedSeries G n := Subgroup.mem_subgroupOf.1 x.2
    have hy : ((y : K) : G) ∈ derivedSeries G n := Subgroup.mem_subgroupOf.1 y.2
    have h2 := congrArg Subtype.val (mul_comm_derivedSeries hbot ⟨_, hx⟩ ⟨_, hy⟩)
    simp only [Subgroup.coe_mul] at h2
    refine Subtype.ext (Subtype.ext ?_)
    simp only [Subgroup.coe_mul]
    exact h2
  -- `A ∩ K` is torsion-free
  have htfAK : IsMulTorsionFree ((derivedSeries G n).subgroupOf K) := by
    haveI := htf
    exact isMulTorsionFree_of_injective (inclKL (derivedSeries G n) K)
      (inclKL_injective (derivedSeries G n) K)
  -- `K / (A ∩ K)` is isomorphic to `M`, hence nilpotent
  have hnilquot : Group.IsNilpotent (K ⧸ (derivedSeries G n).subgroupOf K) := by
    set ψ : K →* M := ((QuotientGroup.mk' (derivedSeries G n)).comp K.subtype).codRestrict M
      (fun x => x.2) with hψ
    have hψsurj : Function.Surjective ψ := by
      rintro ⟨m, hm⟩
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective m
      exact ⟨⟨g, hm⟩, rfl⟩
    have hker : ψ.ker = (derivedSeries G n).subgroupOf K := by
      ext x
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
      constructor
      · intro hx
        exact (QuotientGroup.eq_one_iff _).1 (congrArg Subtype.val hx)
      · intro hx
        exact Subtype.ext ((QuotientGroup.eq_one_iff _).2 hx)
    haveI := hMnil
    refine Group.nilpotent_of_surjective
      ((QuotientGroup.quotientMulEquivOfEq hker.symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective ψ hψsurj)).symm.toMonoidHom
      (MulEquiv.surjective _)
  -- the published core step
  obtain ⟨H, hHnil, hHfi⟩ :=
    isVirtuallyNilpotent_of_isPolycyclic_of_abelian_isMulTorsionFree_isNilpotent_quotient_of_not_hasFreeSubsemigroupOfRankTwo
      (isPolycyclic_subgroup hpoly K)
      (not_hasFreeSubsemigroupOfRankTwo_subgroup hfree K)
      ((derivedSeries G n).subgroupOf K) habAK htfAK hnilquot
  haveI := hHfi
  exact ⟨H.map K.subtype, isNilpotent_map_subtype K H hHnil,
    finiteIndex_map_subtype K H⟩

/-! ### Polycyclic groups are solvable -/

/-- One step of a polycyclic series absorbs the commutator of the larger term, because the
quotient is cyclic and hence commutative. -/
theorem commutator_le_of_isCyclicStep {G : Type*} [Group G] {H K : Subgroup G}
    (h : IsCyclicStep H K) : ⁅K, K⁆ ≤ H := by
  obtain ⟨hle, hnorm, hcyc⟩ := h
  haveI := hnorm
  haveI := hcyc
  rw [Subgroup.commutator_le]
  intro x hx y hy
  have hq : ∀ a b : K ⧸ H.subgroupOf K, a * b = b * a := by
    letI : CommGroup (K ⧸ H.subgroupOf K) := IsCyclic.commGroup
    exact fun a b => mul_comm a b
  have hmem : (⁅(⟨x, hx⟩ : K), (⟨y, hy⟩ : K)⁆) ∈ H.subgroupOf K := by
    rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_commutatorElement,
      commutatorElement_eq_one_iff_mul_comm]
    exact hq _ _
  have hin := Subgroup.mem_subgroupOf.1 hmem
  have hcoe : ((⁅(⟨x, hx⟩ : K), (⟨y, hy⟩ : K)⁆ : K) : G) = ⁅x, y⁆ :=
    map_commutatorElement K.subtype ⟨x, hx⟩ ⟨y, hy⟩
  rwa [hcoe] at hin

/-- A polycyclic group is solvable: its derived series is dominated by the polycyclic series,
term by term. -/
theorem isSolvable_of_isPolycyclic {G : Type*} [Group G] (h : IsPolycyclic G) :
    Group.IsSolvable G := by
  obtain ⟨A, h0, ⟨t, ht⟩, hstep⟩ := exists_chain_of_isPolycyclic h
  have key : ∀ i, derivedSeries G i ≤ A i := by
    intro i
    induction i with
    | zero =>
        rw [derivedSeries_zero, h0]
    | succ n ihn =>
        rw [derivedSeries_succ]
        exact le_trans (Subgroup.commutator_mono ihn ihn)
          (commutator_le_of_isCyclicStep (hstep n))
  exact ⟨⟨t, le_bot_iff.mp (by rw [← ht]; exact key t)⟩⟩

/-! ### The induction -/

/-- Theorem 4.12 for a polycyclic group with no free subsemigroup of rank two, in the shape the
induction needs: the motive quantifies over the group together with its group structure. -/
theorem isVirtuallyNilpotent_aux : ∀ (n : ℕ) (G : Type u) [Group G],
    IsPolycyclic G → ¬ HasFreeSubsemigroupOfRankTwo G → derivedSeries G n = ⊥ →
    Group.IsVirtuallyNilpotent G := by
  intro n
  induction n with
  | zero =>
      intro G _ _ _ hbot
      rw [derivedSeries_zero] at hbot
      refine Group.IsNilpotent.isVirtuallyNilpotent ⟨0, ?_⟩
      simpa using hbot.symm
  | succ n ih =>
      intro G _ hpoly hfree hbot
      have hAn : (derivedSeries G n).Normal := derivedSeries_normal G n
      have habA : ∀ x ∈ derivedSeries G n, ∀ y ∈ derivedSeries G n, x * y = y * x := by
        intro x hx y hy
        simpa using congrArg Subtype.val (mul_comm_derivedSeries hbot ⟨x, hx⟩ ⟨y, hy⟩)
      -- remove the torsion of the last nontrivial derived term
      have hTn : (torsionSub (derivedSeries G n) habA).Normal := torsionSub_normal _ habA
      have hTf : Finite (torsionSub (derivedSeries G n) habA) :=
        finite_torsionSub hpoly _ habA
      refine isVirtuallyNilpotent_of_finite_abelian_normal_quotient
        (torsionSub (derivedSeries G n) habA)
        (fun x hx y hy => habA x (torsionSub_le _ habA hx) y (torsionSub_le _ habA hy)) ?_
      -- in the quotient the term is torsion-free, so the torsion-free case applies
      have hmk := QuotientGroup.mk'_surjective (torsionSub (derivedSeries G n) habA)
      refine isVirtuallyNilpotent_of_torsionFree (n := n) (fun Q _ => ih Q)
        (isPolycyclic_of_surjective hpoly _ hmk)
        (not_hasFreeSubsemigroupOfRankTwo_quotient _ hfree) ?_ ?_
      · rw [← map_derivedSeries_eq
            (f := QuotientGroup.mk' (torsionSub (derivedSeries G n) habA)) hmk, hbot]
        simp
      · have heq : (derivedSeries G n).map
              (QuotientGroup.mk' (torsionSub (derivedSeries G n) habA))
            = derivedSeries (G ⧸ torsionSub (derivedSeries G n) habA) n :=
          map_derivedSeries_eq hmk n
        have := isMulTorsionFree_map_torsionSub (derivedSeries G n) habA
        exact heq ▸ this

/-- **Rosenblatt, Theorem 4.12**, one half: a polycyclic group with no free subsemigroup of rank
two is almost nilpotent.  Equivalently, the dichotomy of Theorem 4.12 itself. -/
theorem isVirtuallyNilpotent_of_isPolycyclic_of_not_hasFreeSubsemigroupOfRankTwo
    {G : Type u} [Group G] (hpoly : IsPolycyclic G)
    (hfree : ¬ HasFreeSubsemigroupOfRankTwo G) : Group.IsVirtuallyNilpotent G := by
  obtain ⟨n, hn⟩ := (isSolvable_of_isPolycyclic hpoly).solvable
  exact isVirtuallyNilpotent_aux n G hpoly hfree hn

/-- **Rosenblatt, Theorem 4.12**: a polycyclic group is almost nilpotent or contains a free
subsemigroup of rank two. -/
theorem dichotomy_of_isPolycyclic
    {G : Type u} [Group G] (hpoly : IsPolycyclic G) :
    Group.IsVirtuallyNilpotent G ∨ HasFreeSubsemigroupOfRankTwo G := by
  by_cases hfree : HasFreeSubsemigroupOfRankTwo G
  · exact Or.inr hfree
  · exact Or.inl (isVirtuallyNilpotent_of_isPolycyclic_of_not_hasFreeSubsemigroupOfRankTwo
      hpoly hfree)

end Rosenblatt

theorem solution {G : Type*} [Group G] (h : MilnorWolf.IsPolycyclic G) :
    Group.IsVirtuallyNilpotent G ∨ Chou.HasFreeSubsemigroupOfRankTwo G :=
  Rosenblatt.dichotomy_of_isPolycyclic h
