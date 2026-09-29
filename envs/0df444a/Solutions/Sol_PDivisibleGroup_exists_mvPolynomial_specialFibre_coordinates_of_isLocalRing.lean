-- Prove2me | solution 1 for PDivisibleGroup.exists_mvPolynomial_specialFibre_coordinates_of_isLocalRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/a1fcc01b-eca6-526c-9ff0-9cfbae1c64a2

import Mathlib
import Definitions.Def_PDivisibleGroup_Basic
import Theorems.Thm_PDivisibleGroup_specialFibre_tower_of_isLocalRing
import Theorems.Thm_PDivisibleGroup_ker_aeval_quotient_span_pow_augIdeal_eq_span_X_pow_of_isLocalRing
import Theorems.Thm_PDivisibleGroup_Hopf_nsmulAlgHom_sub_nsmul_mem_augIdeal_sq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PDivisibleGroup_exists_mvPolynomial_specialFibre_coordinates_of_isLocalRing
p2m_attr_erase "instance" "MonoidAlgebra.instModuleFiniteOfCartier CartierDual.instCoalgebra CartierDual.instModuleFinite CartierDual.instBialgebra CartierDual.instFunLike CartierDual.instRing CartierDual.instLinearMapClass CartierDual.instCommRing CartierDual.instIsCocomm MonoidAlgebra.instModuleFreeOfCartier CartierDual.instModuleFree CartierDual.instHopfAlgebra CartierDual.instAlgebra HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra HopfAlgebra.IsHopfTower.refl"
p2m_attr_erase "simp" "CartierDual.toDual_ofDual CartierDual.algebraMap_apply CartierDual.antipode_apply CartierDual.one_apply CartierDual.toDual_apply CartierDual.ofDual_toDual CartierDual.ofDual_apply CartierDual.counit_apply HopfAlgebra.canAlgHom_tmul HopfAlgebra.canMap_tmul HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul HopfAlgebra.HopfTower.quotientMap_mk HopfAlgebra.IsHopfSubalgebra.ι₂_comulK HopfAlgebra.IsHopfTower.toBialgHom_apply HopfAlgebra.IsHopfTower.reprMap_right HopfAlgebra.IsHopfSubalgebra.counitK_apply HopfAlgebra.IsHopfSubalgebra.coe_antipodeK HopfAlgebra.HopfTower.galoisInv_tmul HopfAlgebra.HopfTower.galoisFwd_tmul HopfAlgebra.mem_augIdeal HopfAlgebra.IsHopfTower.reprMap_index HopfAlgebra.HopfTower.antipodeAlgHom_apply HopfAlgebra.IsHopfTower.reprMap_left HopfAlgebra.IsHopfSubalgebra.ι₂_tmul HopfAlgebra.HopfTower.θ₁_tmul HopfAlgebra.HopfTower.fwdB_apply HopfAlgebra.HopfTower.invQuot_mk HopfAlgebra.HopfTower.translateEquiv_apply HopfAlgebra.HopfTower.θ₂_tmul HopfAlgebra.IsHopfSubalgebra.ι₃_tmul"

set_option autoImplicit false

open scoped TensorProduct
open Function PDivisibleGroup.Hopf

universe u v

namespace C12Body

section Level

variable (p : ℕ) [Fact p.Prime] {A : Type v} [CommRing A] [HopfAlgebra (ZMod p) A]
  [Module.Finite (ZMod p) A]

omit [Module.Finite (ZMod p) A] in

private theorem augIdeal_ne_top : augIdeal (ZMod p) A ≠ ⊤ := by
  intro h
  have h1 : (1 : A) ∈ augIdeal (ZMod p) A := h ▸ Submodule.mem_top
  rw [mem_augIdeal_iff, Bialgebra.counit_one] at h1
  exact one_ne_zero h1

private theorem exists_span_pow_augIdeal_eq_bot [IsLocalRing A] :
    ∃ N : ℕ, Ideal.span ((fun a : A => a ^ p ^ N) '' (augIdeal (ZMod p) A : Set A)) = ⊥ := by
  haveI : IsArtinianRing A := IsArtinianRing.of_finite (ZMod p) A
  obtain ⟨M, hM⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := A)
  rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top] at hM
  refine ⟨M, ?_⟩
  rw [Ideal.span_eq_bot]
  rintro _ ⟨a, ha, rfl⟩
  have hle : augIdeal (ZMod p) A ≤ IsLocalRing.maximalIdeal A :=
    IsLocalRing.le_maximalIdeal (augIdeal_ne_top p)
  have hpow : a ^ M = 0 := by
    have := Ideal.pow_mem_pow (hle ha) M
    rw [hM] at this
    exact (Submodule.mem_bot _).1 this
  have hMle : M ≤ p ^ M := (Nat.lt_pow_self (Fact.out : p.Prime).one_lt).le
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hMle
  change a ^ p ^ M = 0
  rw [hk, pow_add, hpow, zero_mul]

omit [Module.Finite (ZMod p) A] in

private theorem torsionIdeal_le_sq {v : ℕ} (hv : 1 ≤ v) :
    torsionIdeal (ZMod p) A (p ^ v) ≤ augIdeal (ZMod p) A ^ 2 := by
  rw [torsionIdeal, Ideal.map_le_iff_le_comap]
  intro a ha
  have h := nsmulAlgHom_sub_nsmul_mem_augIdeal_sq (R := ZMod p) (p ^ v) ha
  have h0 : (p ^ v) • a = 0 := by
    rw [← Nat.cast_smul_eq_nsmul (ZMod p), Nat.cast_pow, ZMod.natCast_self, zero_pow (by omega), zero_smul]
  rwa [h0, sub_zero] at h

end Level

section Trans

variable (p : ℕ) [Fact p.Prime] {A : Type v} [CommRing A] [HopfAlgebra (ZMod p) A]
  {B : Type v} [CommRing B] [HopfAlgebra (ZMod p) B] (s : B →ₐc[ZMod p] A)

private theorem map_mem_augIdeal {b : B} (hb : b ∈ augIdeal (ZMod p) B) : s b ∈ augIdeal (ZMod p) A := by
  rw [mem_augIdeal_iff] at hb ⊢
  rw [CoalgHomClass.counit_comp_apply, hb]

private theorem exists_mem_augIdeal_map_eq (hs : Surjective s) {a : A} (ha : a ∈ augIdeal (ZMod p) A) :
    ∃ b ∈ augIdeal (ZMod p) B, s b = a := by
  obtain ⟨b, rfl⟩ := hs a
  refine ⟨b - algebraMap (ZMod p) B (Coalgebra.counit (R := ZMod p) b),
    sub_algebraMap_counit_mem_augIdeal (ZMod p) B b, ?_⟩
  rw [mem_augIdeal_iff, CoalgHomClass.counit_comp_apply] at ha
  rw [map_sub, AlgHomClass.commutes, ha, map_zero, sub_zero]

private theorem map_augIdeal_eq (hs : Surjective s) :
    (augIdeal (ZMod p) B).map (s : B →ₐ[ZMod p] A) = augIdeal (ZMod p) A := by
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro b hb
    exact map_mem_augIdeal p s hb
  · intro a ha
    obtain ⟨b, hb, rfl⟩ := exists_mem_augIdeal_map_eq p s hs ha
    exact Ideal.mem_map_of_mem _ hb

private theorem map_span_pow_le (n : ℕ) :
    (Ideal.span ((fun b : B => b ^ p ^ n) '' (augIdeal (ZMod p) B : Set B))).map (s : B →ₐ[ZMod p] A) ≤
      Ideal.span ((fun a : A => a ^ p ^ n) '' (augIdeal (ZMod p) A : Set A)) := by
  rw [Ideal.map_span, Ideal.span_le]
  rintro _ ⟨_, ⟨b, hb, rfl⟩, rfl⟩
  refine Ideal.subset_span ⟨s b, map_mem_augIdeal p s hb, ?_⟩
  change s b ^ p ^ n = (s : B →ₐ[ZMod p] A) (b ^ p ^ n)
  rw [map_pow]; rfl

private theorem span_toCotangent_eq_top_of_lift (hs : Surjective s)
    (hker : RingHom.ker s ≤ augIdeal (ZMod p) B ^ 2)
    {d : ℕ} (x : Fin d → A) (hx : ∀ i, x i ∈ augIdeal (ZMod p) A)
    (hspan : Submodule.span (ZMod p) (Set.range fun i =>
      (augIdeal (ZMod p) A).toCotangent ⟨x i, hx i⟩) = ⊤)
    (y : Fin d → B) (hy : ∀ i, y i ∈ augIdeal (ZMod p) B) (hsy : ∀ i, s (y i) = x i) :
    Submodule.span (ZMod p) (Set.range fun i =>
      (augIdeal (ZMod p) B).toCotangent ⟨y i, hy i⟩) = ⊤ := by
  classical
  rw [eq_top_iff]
  rintro z -
  obtain ⟨⟨b, hb⟩, rfl⟩ := (augIdeal (ZMod p) B).toCotangent_surjective z

  have hsb : (augIdeal (ZMod p) A).toCotangent ⟨s b, map_mem_augIdeal p s hb⟩ ∈
      Submodule.span (ZMod p) (Set.range fun i => (augIdeal (ZMod p) A).toCotangent ⟨x i, hx i⟩) := by
    rw [hspan]; exact Submodule.mem_top
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (ZMod p)).1 hsb

  have h2 : s b - ∑ i, c i • x i ∈ augIdeal (ZMod p) A ^ 2 := by
    have h1 : (augIdeal (ZMod p) A).toCotangent ⟨s b, map_mem_augIdeal p s hb⟩ =
        (augIdeal (ZMod p) A).toCotangent (∑ i, c i • (⟨x i, hx i⟩ : augIdeal (ZMod p) A)) := by
      rw [map_sum, ← hc]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [LinearMap.map_smul_of_tower]
    have h3 := ((Ideal.toCotangent_eq _).1 h1)
    push_cast at h3
    exact h3

  have hmem : s (b - ∑ i, c i • y i) ∈ ((augIdeal (ZMod p) B) ^ 2).map (s : B →ₐ[ZMod p] A) := by
    rw [Ideal.map_pow, map_augIdeal_eq p s hs]
    have : s (b - ∑ i, c i • y i) = s b - ∑ i, c i • x i := by
      rw [map_sub, map_sum]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, hsy]
    rw [this]
    exact h2
  obtain ⟨q, hq, hsq⟩ := (Ideal.mem_map_iff_of_surjective (s : B →ₐ[ZMod p] A) hs).1 hmem

  have hk : b - ∑ i, c i • y i - q ∈ (augIdeal (ZMod p) B) ^ 2 := by
    refine hker ?_
    rw [RingHom.mem_ker, map_sub, sub_eq_zero]
    exact hsq.symm
  have hb2 : b - ∑ i, c i • y i ∈ (augIdeal (ZMod p) B) ^ 2 := by
    have := add_mem hk hq
    rwa [sub_add_cancel] at this

  have h4 : (augIdeal (ZMod p) B).toCotangent ⟨b, hb⟩ =
      (augIdeal (ZMod p) B).toCotangent (∑ i, c i • (⟨y i, hy i⟩ : augIdeal (ZMod p) B)) := by
    rw [Ideal.toCotangent_eq]
    push_cast
    exact hb2
  rw [h4, map_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [LinearMap.map_smul_of_tower]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

end Trans

section Tower

variable (p : ℕ) [Fact p.Prime] (h₀ : ℕ)
  (H : ℕ → Type v) [∀ v, CommRing (H v)] [∀ v, HopfAlgebra (ZMod p) (H v)]
  [∀ v, Coalgebra.IsCocomm (ZMod p) (H v)] [∀ v, Module.Finite (ZMod p) (H v)]
  (s : ∀ v, H (v + 1) →ₐc[ZMod p] H v) (hs : ∀ v, Surjective (s v))
  (hrankH : ∀ v, Module.finrank (ZMod p) (H v) = p ^ (v * h₀))
  (hkerH : ∀ v, RingHom.ker (s v) = torsionIdeal (ZMod p) (H (v + 1)) (p ^ v))
  (hlocH : ∀ v, IsLocalRing (H v))

private noncomputable def T (v : ℕ) : ∀ w : ℕ, H (v + w) →ₐc[ZMod p] H v
  | 0 => BialgHom.id (ZMod p) (H v)
  | w + 1 => (T v w).comp (s (v + w))

omit [∀ v, Coalgebra.IsCocomm (ZMod p) (H v)] [∀ v, Module.Finite (ZMod p) (H v)] in
private theorem T_zero (v : ℕ) : T p H s v 0 = BialgHom.id (ZMod p) (H v) := rfl

omit [∀ v, Coalgebra.IsCocomm (ZMod p) (H v)] [∀ v, Module.Finite (ZMod p) (H v)] in
private theorem T_succ (v w : ℕ) : T p H s v (w + 1) = (T p H s v w).comp (s (v + w)) := rfl

include hs in
omit [∀ v, Coalgebra.IsCocomm (ZMod p) (H v)] [∀ v, Module.Finite (ZMod p) (H v)] in
private theorem T_surjective (v : ℕ) : ∀ w, Surjective (T p H s v w)
  | 0 => fun a => ⟨a, rfl⟩
  | w + 1 => by
    rw [T_succ]
    exact (T_surjective v w).comp (hs (v + w))

private noncomputable def dim : ℕ := Module.finrank (ZMod p) (augIdeal (ZMod p) (H 1)).Cotangent

include hs hkerH in
omit [∀ v, Coalgebra.IsCocomm (ZMod p) (H v)] in

private theorem exists_coords :
    ∃ x : ∀ v, Fin (dim p H) → augIdeal (ZMod p) (H v),
      (∀ v i, s v (x (v + 1) i) = x v i) ∧
      (∀ n, Submodule.span (ZMod p) (Set.range fun i =>
        (augIdeal (ZMod p) (H (n + 1))).toCotangent (x (n + 1) i)) = ⊤) := by
  classical

  haveI : IsNoetherianRing (H 1) := isNoetherian_of_tower (ZMod p) inferInstance
  haveI : Module.Finite (H 1) (augIdeal (ZMod p) (H 1)).Cotangent :=
    Module.Finite.of_surjective _ (augIdeal (ZMod p) (H 1)).toCotangent_surjective
  haveI : Module.Finite (ZMod p) (augIdeal (ZMod p) (H 1)).Cotangent :=
    Module.Finite.trans (H 1) (augIdeal (ZMod p) (H 1)).Cotangent
  let b := Module.finBasisOfFinrankEq (ZMod p) (augIdeal (ZMod p) (H 1)).Cotangent (rfl : _ = dim p H)
  choose x₁ hx₁ using fun i => (augIdeal (ZMod p) (H 1)).toCotangent_surjective (b i)

  have step : ∀ (v : ℕ) (xv : Fin (dim p H) → augIdeal (ZMod p) (H v)),
      ∃ y : Fin (dim p H) → augIdeal (ZMod p) (H (v + 1)), ∀ i, s v (y i) = xv i := by
    intro v xv
    have h1 : ∀ i, ∃ y : augIdeal (ZMod p) (H (v + 1)), s v y = xv i := fun i => by
      obtain ⟨c, hc, hsc⟩ := exists_mem_augIdeal_map_eq p (s v) (hs v) (xv i).2
      exact ⟨⟨c, hc⟩, hsc⟩
    choose y hy using h1
    exact ⟨y, hy⟩
  choose lift hlift using step

  let seq : ∀ n : ℕ, Fin (dim p H) → augIdeal (ZMod p) (H (n + 1)) :=
    fun n => Nat.rec (motive := fun n => Fin (dim p H) → augIdeal (ZMod p) (H (n + 1))) x₁
      (fun n xn => lift (n + 1) xn) n
  have seq_succ : ∀ n, seq (n + 1) = lift (n + 1) (seq n) := fun n => rfl
  let x : ∀ v, Fin (dim p H) → augIdeal (ZMod p) (H v) :=
    fun v => Nat.rec (motive := fun v => Fin (dim p H) → augIdeal (ZMod p) (H v))
      (fun i => ⟨s 0 (seq 0 i), map_mem_augIdeal p (s 0) (seq 0 i).2⟩) (fun n _ => seq n) v
  have x_zero : ∀ i, (x 0 i : H 0) = s 0 (seq 0 i) := fun i => rfl
  have x_succ : ∀ n, x (n + 1) = seq n := fun n => rfl
  refine ⟨x, ?_, ?_⟩
  · intro v i
    cases v with
    | zero => rw [x_zero]
    | succ n => rw [x_succ (n + 1), x_succ n, seq_succ, hlift]
  · intro n
    induction n with
    | zero =>
      rw [x_succ]
      change Submodule.span (ZMod p) (Set.range fun i => (augIdeal (ZMod p) (H 1)).toCotangent (x₁ i)) = ⊤
      simp_rw [hx₁]
      exact b.span_eq
    | succ n ih =>
      rw [x_succ (n + 1), seq_succ]
      have hker : RingHom.ker (s (n + 1)) ≤ augIdeal (ZMod p) (H (n + 1 + 1)) ^ 2 := by
        rw [hkerH]
        exact torsionIdeal_le_sq p (by omega)
      have := span_toCotangent_eq_top_of_lift p (s (n + 1)) (hs (n + 1)) hker
        (fun i => (seq n i : H (n + 1))) (fun i => (seq n i).2) ?_
        (fun i => (lift (n + 1) (seq n) i : H (n + 1 + 1))) (fun i => (lift (n + 1) (seq n) i).2)
        (fun i => hlift (n + 1) (seq n) i)
      · exact this
      · rw [x_succ n] at ih
        exact ih

omit [∀ v, Coalgebra.IsCocomm (ZMod p) (H v)] [∀ v, Module.Finite (ZMod p) (H v)] in
private theorem T_apply_coord {d : ℕ} (x : ∀ v, Fin d → H v) (hxt : ∀ v i, s v (x (v + 1) i) = x v i)
    (v : ℕ) : ∀ (w : ℕ) (i : Fin d), T p H s v w (x (v + w) i) = x v i
  | 0, i => rfl
  | w + 1, i => by
    rw [T_succ, BialgHom.comp_apply]
    change T p H s v w (s (v + w) (x (v + w + 1) i)) = x v i
    rw [hxt, T_apply_coord x hxt v w i]

include hs hrankH hkerH hlocH in

private theorem exists_coordinates :
    ∃ (d : ℕ) (x : ∀ v, Fin d → H v),
      (∀ v i, s v (x (v + 1) i) = x v i) ∧
      (∀ v i, Coalgebra.counit (R := ZMod p) (x v i) = 0) ∧
      (∀ v, Surjective (MvPolynomial.aeval (x v) : MvPolynomial (Fin d) (ZMod p) →ₐ[ZMod p] H v)) ∧
      (∀ N : ℕ, ∃ v, RingHom.ker (MvPolynomial.aeval (x v) : MvPolynomial (Fin d) (ZMod p) →ₐ[ZMod p] H v) ≤
        (Ideal.span (Set.range (MvPolynomial.X : Fin d → MvPolynomial (Fin d) (ZMod p)))) ^ N) := by
  classical
  obtain ⟨x, hxt, hspan⟩ := exists_coords p H s hs hkerH
  have hxt' : ∀ v i, s v ((fun v i => (x v i : H v)) (v + 1) i) = (fun v i => (x v i : H v)) v i :=
    fun v i => hxt v i
  refine ⟨dim p H, fun v i => (x v i : H v), hxt, fun v i => (x v i).2, fun v => ?_, fun N => ?_⟩
  ·
    haveI := hlocH v
    obtain ⟨N, hN⟩ := exists_span_pow_augIdeal_eq_bot p (A := H v)
    have hC1 := (PDivisibleGroup.ker_aeval_quotient_span_pow_augIdeal_eq_span_X_pow_of_isLocalRing p h₀ H s hs
      hrankH hkerH hlocH N (v + N + 1) (by omega) (dim p H) rfl (fun i => (x (v + N + 1) i : H (v + N + 1)))
      (fun i => (x (v + N + 1) i).2) (hspan (v + N))).1
    intro a
    obtain ⟨c, rfl⟩ := T_surjective p H s hs v (N + 1) a
    obtain ⟨P, hP⟩ := hC1 (Ideal.Quotient.mk _ c)
    rw [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq] at hP
    refine ⟨P, ?_⟩

    have h1 : (T p H s v (N + 1) : H (v + (N + 1)) →ₐ[ZMod p] H v)
        (MvPolynomial.aeval (fun i => (x (v + N + 1) i : H (v + N + 1))) P) =
        MvPolynomial.aeval (fun i => (x v i : H v)) P := by
      rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval]
      congr 2
      funext i
      exact T_apply_coord p H s (fun v i => (x v i : H v)) hxt' v (N + 1) i

    have h2 : (T p H s v (N + 1) : H (v + (N + 1)) →ₐ[ZMod p] H v)
        (MvPolynomial.aeval (fun i => (x (v + N + 1) i : H (v + N + 1))) P - c) = 0 := by
      have := map_span_pow_le p (T p H s v (N + 1)) N (Ideal.mem_map_of_mem _ hP)
      rw [hN] at this
      exact (Submodule.mem_bot _).1 this
    rw [map_sub, sub_eq_zero, h1] at h2
    exact h2.symm ▸ rfl
  ·
    refine ⟨N + 1, ?_⟩
    have hC1 := (PDivisibleGroup.ker_aeval_quotient_span_pow_augIdeal_eq_span_X_pow_of_isLocalRing p h₀ H s hs
      hrankH hkerH hlocH (N + 1) (N + 1) le_rfl (dim p H) rfl (fun i => (x (N + 1) i : H (N + 1)))
      (fun i => (x (N + 1) i).2) (hspan N)).2
    intro P hP
    have h1 : P ∈ Ideal.span (Set.range fun i : Fin (dim p H) =>
        (MvPolynomial.X i : MvPolynomial (Fin (dim p H)) (ZMod p)) ^ p ^ (N + 1)) := by
      rw [← hC1, RingHom.mem_ker, AlgHom.comp_apply]
      rw [RingHom.mem_ker] at hP
      rw [hP, map_zero]
    have hNle : N ≤ p ^ (N + 1) :=
      (Nat.lt_pow_self (Fact.out : p.Prime).one_lt).le.trans
        (Nat.pow_le_pow_right (Fact.out : p.Prime).pos (Nat.le_succ N))
    refine Ideal.pow_le_pow_right hNle ?_
    have hle : Ideal.span (Set.range fun i : Fin (dim p H) =>
        (MvPolynomial.X i : MvPolynomial (Fin (dim p H)) (ZMod p)) ^ p ^ (N + 1)) ≤
        (Ideal.span (Set.range (MvPolynomial.X : Fin (dim p H) → MvPolynomial (Fin (dim p H)) (ZMod p)))) ^
          p ^ (N + 1) := by
      rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      exact Ideal.pow_mem_pow (Ideal.subset_span (Set.mem_range_self i)) _
    exact hle h1

end Tower

end C12Body

open C12Body in
theorem solution
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    [Algebra 𝓞 (ZMod p)] (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)})
    [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞]
    (h₀ : ℕ) (R₀ : ℕ → Type v) [∀ v, CommRing (R₀ v)] [∀ v, HopfAlgebra 𝓞 (R₀ v)]
    [∀ v, Coalgebra.IsCocomm 𝓞 (R₀ v)] [∀ v, Module.Free 𝓞 (R₀ v)] [∀ v, Module.Finite 𝓞 (R₀ v)]
    (t₀ : ∀ v, R₀ (v + 1) →ₐc[𝓞] R₀ v) (ht₀ : ∀ v, Function.Surjective (t₀ v))
    (hrank₀ : ∀ v, Module.finrank 𝓞 (R₀ v) = p ^ (v * h₀))
    (hker₀ : ∀ v, RingHom.ker (t₀ v) = PDivisibleGroup.Hopf.torsionIdeal 𝓞 (R₀ (v + 1)) (p ^ v))
    (hconn : ∀ v, IsLocalRing (R₀ v)) :
    ∃ (d : ℕ) (πbar : ∀ v, MvPolynomial (Fin d) (ZMod p) →ₐ[ZMod p] TensorProduct 𝓞 (ZMod p) (R₀ v)),
      (∀ v, Function.Surjective (πbar v)) ∧
      (∀ v, (Algebra.TensorProduct.map (AlgHom.id (ZMod p) (ZMod p)) (t₀ v : R₀ (v + 1) →ₐ[𝓞] R₀ v)).comp
        (πbar (v + 1)) = πbar v) ∧
      (∀ v i, Coalgebra.counit (R := ZMod p) (A := TensorProduct 𝓞 (ZMod p) (R₀ v))
        (πbar v (MvPolynomial.X i)) = 0) ∧
      (∀ N : ℕ, ∃ v, RingHom.ker (πbar v) ≤
        (Ideal.span (Set.range (MvPolynomial.X : Fin d → MvPolynomial (Fin d) (ZMod p)))) ^ N) := by
  classical

  obtain ⟨hsurjA, hrankH, hkerH, hlocH⟩ :=
    PDivisibleGroup.specialFibre_tower_of_isLocalRing p hp hker h₀ R₀ t₀ ht₀ hrank₀ hker₀ hconn
  let s : ∀ v, TensorProduct 𝓞 (ZMod p) (R₀ (v + 1)) →ₐc[ZMod p] TensorProduct 𝓞 (ZMod p) (R₀ v) :=
    fun v => Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (t₀ v)
  have hcoe : ∀ v z, s v z =
      Algebra.TensorProduct.map (AlgHom.id (ZMod p) (ZMod p)) (t₀ v : R₀ (v + 1) →ₐ[𝓞] R₀ v) z := by
    intro v z
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul a b => rw [Bialgebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul]; rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  have hs : ∀ v, Function.Surjective (s v) := fun v z => by
    obtain ⟨w, hw⟩ := hsurjA v z
    exact ⟨w, by rw [hcoe, hw]⟩

  obtain ⟨d, x, hxt, hxε, hxs, hxk⟩ :=
    exists_coordinates p h₀ (fun v => TensorProduct 𝓞 (ZMod p) (R₀ v)) s hs hrankH hkerH hlocH
  refine ⟨d, fun v => MvPolynomial.aeval (x v), hxs, fun v => ?_, fun v i => ?_, hxk⟩
  · refine MvPolynomial.algHom_ext fun i => ?_
    rw [AlgHom.comp_apply, MvPolynomial.aeval_X, MvPolynomial.aeval_X, ← hcoe, hxt]
  · rw [MvPolynomial.aeval_X]
    exact hxε v i

end S_PDivisibleGroup_exists_mvPolynomial_specialFibre_coordinates_of_isLocalRing
end P2MW
export P2MW.S_PDivisibleGroup_exists_mvPolynomial_specialFibre_coordinates_of_isLocalRing (solution)
