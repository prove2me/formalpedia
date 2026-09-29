-- Prove2me | solution 1 for PDivisibleGroup.exists_surjective_mvPowerSeries_comp_eq_of_isLocalRing_zmodp
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/9c115bce-5664-5d75-a9fe-379c75cfb162

import Mathlib
import Definitions.Def_PDivisibleGroup_Basic
import Definitions.Def_MvFormalGroup_PointsV2
import Theorems.Thm_PDivisibleGroup_ker_aeval_quotient_span_pow_augIdeal_eq_span_X_pow_of_isLocalRing
import Theorems.Thm_PDivisibleGroup_Hopf_nsmulAlgHom_sub_nsmul_mem_augIdeal_sq
import Theorems.Thm_MvFormalGroup_algHom_apply_eq_adicEval_of_forall_apply_X_mem_radical
import Theorems.Thm_MvPowerSeries_mem_pow_span_X_of_coeff_eq_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PDivisibleGroup_exists_surjective_mvPowerSeries_comp_eq_of_isLocalRing_zmodp
p2m_attr_erase "instance" "MonoidAlgebra.instModuleFiniteOfCartier CartierDual.instCoalgebra CartierDual.instModuleFinite CartierDual.instBialgebra CartierDual.instFunLike CartierDual.instRing CartierDual.instLinearMapClass CartierDual.instCommRing CartierDual.instIsCocomm MonoidAlgebra.instModuleFreeOfCartier CartierDual.instModuleFree CartierDual.instHopfAlgebra CartierDual.instAlgebra HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra HopfAlgebra.IsHopfTower.refl"
p2m_attr_erase "simp" "CartierDual.toDual_ofDual CartierDual.algebraMap_apply CartierDual.antipode_apply CartierDual.one_apply CartierDual.toDual_apply CartierDual.ofDual_toDual CartierDual.ofDual_apply CartierDual.counit_apply HopfAlgebra.canAlgHom_tmul HopfAlgebra.canMap_tmul HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul HopfAlgebra.HopfTower.quotientMap_mk HopfAlgebra.IsHopfSubalgebra.ι₂_comulK HopfAlgebra.IsHopfTower.toBialgHom_apply HopfAlgebra.IsHopfTower.reprMap_right HopfAlgebra.IsHopfSubalgebra.counitK_apply HopfAlgebra.IsHopfSubalgebra.coe_antipodeK HopfAlgebra.HopfTower.galoisInv_tmul HopfAlgebra.HopfTower.galoisFwd_tmul HopfAlgebra.mem_augIdeal HopfAlgebra.IsHopfTower.reprMap_index HopfAlgebra.HopfTower.antipodeAlgHom_apply HopfAlgebra.IsHopfTower.reprMap_left HopfAlgebra.IsHopfSubalgebra.ι₂_tmul HopfAlgebra.HopfTower.θ₁_tmul HopfAlgebra.HopfTower.fwdB_apply HopfAlgebra.HopfTower.invQuot_mk HopfAlgebra.HopfTower.translateEquiv_apply HopfAlgebra.HopfTower.θ₂_tmul HopfAlgebra.IsHopfSubalgebra.ι₃_tmul"

set_option autoImplicit false

open scoped TensorProduct
open Function PDivisibleGroup.Hopf

universe v

namespace CoordField

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
    ∃ (d : ℕ) (x : ∀ v, Fin d → H v), d = dim p H ∧
      (∀ v i, s v (x (v + 1) i) = x v i) ∧
      (∀ v i, Coalgebra.counit (R := ZMod p) (x v i) = 0) ∧
      (∀ v, Surjective (MvPolynomial.aeval (x v) : MvPolynomial (Fin d) (ZMod p) →ₐ[ZMod p] H v)) ∧
      (∀ N : ℕ, ∃ v, RingHom.ker (MvPolynomial.aeval (x v) : MvPolynomial (Fin d) (ZMod p) →ₐ[ZMod p] H v) ≤
        (Ideal.span (Set.range (MvPolynomial.X : Fin d → MvPolynomial (Fin d) (ZMod p)))) ^ N) := by
  classical
  obtain ⟨x, hxt, hspan⟩ := exists_coords p H s hs hkerH
  have hxt' : ∀ v i, s v ((fun v i => (x v i : H v)) (v + 1) i) = (fun v i => (x v i : H v)) v i :=
    fun v i => hxt v i
  refine ⟨dim p H, fun v i => (x v i : H v), rfl, hxt, fun v i => (x v i).2, fun v => ?_, fun N => ?_⟩
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

section PS

variable (p : ℕ) [Fact p.Prime] {d : ℕ}

private theorem coeff_eq_zero_of_mem_pow {N : ℕ} {G : MvPowerSeries (Fin d) (ZMod p)}
    (hG : G ∈ (Ideal.span (Set.range (MvPowerSeries.X : Fin d → MvPowerSeries (Fin d) (ZMod p)))) ^ N)
    {m : Fin d →₀ ℕ} (hm : m.degree < N) : MvPowerSeries.coeff m G = 0 := by
  classical

  let K : ℕ → Ideal (MvPowerSeries (Fin d) (ZMod p)) := fun n =>
    { carrier := {G | ∀ m : Fin d →₀ ℕ, m.degree < n → MvPowerSeries.coeff m G = 0}
      add_mem' := fun {a b} ha hb m hm => by rw [map_add, ha m hm, hb m hm, add_zero]
      zero_mem' := fun m _ => by rw [map_zero]
      smul_mem' := fun c {a} ha m hm => by
        rw [smul_eq_mul, MvPowerSeries.coeff_mul]
        refine Finset.sum_eq_zero fun q hq => ?_
        rw [Finset.HasAntidiagonal.mem_antidiagonal] at hq
        have : q.2.degree < n := lt_of_le_of_lt (by rw [← hq, map_add]; exact Nat.le_add_left _ _) hm
        rw [ha q.2 this, mul_zero] }
  have hK : ∀ n, (Ideal.span (Set.range (MvPowerSeries.X : Fin d → MvPowerSeries (Fin d) (ZMod p)))) ^ n ≤ K n := by
    intro n
    induction n with
    | zero => intro G _ m hm; exact absurd hm (Nat.not_lt_zero _)
    | succ n ih =>
      rw [pow_succ]
      refine (Ideal.mul_mono_left ih).trans ?_
      rw [Ideal.mul_le]
      intro a ha b hb
      refine Submodule.span_induction (p := fun b _ => a * b ∈ K (n + 1)) ?_ ?_ ?_ ?_ hb
      · rintro _ ⟨i, rfl⟩ m hm
        rw [MvPowerSeries.coeff_mul]
        refine Finset.sum_eq_zero fun q hq => ?_
        rw [Finset.HasAntidiagonal.mem_antidiagonal] at hq
        rw [MvPowerSeries.coeff_X]
        split_ifs with h
        · have : q.1.degree < n := by
            have h1 : m.degree = q.1.degree + q.2.degree := by rw [← hq, map_add]
            rw [h, Finsupp.degree_single] at h1
            omega
          rw [ha q.1 this, zero_mul]
        · rw [mul_zero]
      · intro m _; rw [mul_zero, map_zero]
      · intro u w _ _ hu hw m hm; rw [mul_add, map_add, hu m hm, hw m hm, add_zero]
      · intro c u _ hu m hm
        rw [smul_eq_mul, mul_left_comm]
        exact (K (n + 1)).smul_mem c hu m hm
  exact hK N hG m hm

variable {A : Type v} [CommRing A] [Algebra (ZMod p) A]

private noncomputable def evalPS (x : Fin d → A) (hx : ∀ i, IsNilpotent (x i)) :
    MvPowerSeries (Fin d) (ZMod p) →ₐ[ZMod p] A :=
  MvFormalGroup.adicEvalAlgHom (⊥ : Ideal A) (x := x) fun i => by
    obtain ⟨n, hn⟩ := hx i; exact ⟨n, by rw [hn]; exact Submodule.zero_mem _⟩

private theorem evalPS_coe (x : Fin d → A) (hx : ∀ i, IsNilpotent (x i)) (P : MvPolynomial (Fin d) (ZMod p)) :
    evalPS p x hx (P : MvPowerSeries (Fin d) (ZMod p)) = MvPolynomial.aeval x P := by
  rw [evalPS, MvFormalGroup.coe_adicEvalAlgHom, MvFormalGroup.adicEval_coe]

private theorem evalPS_X (x : Fin d → A) (hx : ∀ i, IsNilpotent (x i)) (i : Fin d) :
    evalPS p x hx (MvPowerSeries.X i) = x i := by
  rw [evalPS, MvFormalGroup.coe_adicEvalAlgHom, MvFormalGroup.adicEval_X]

private theorem eq_evalPS (φ : MvPowerSeries (Fin d) (ZMod p) →ₐ[ZMod p] A) (hφ : ∀ i, IsNilpotent (φ (MvPowerSeries.X i))) :
    φ = evalPS p (fun i => φ (MvPowerSeries.X i)) hφ := by
  refine AlgHom.ext fun G => ?_
  rw [evalPS, MvFormalGroup.coe_adicEvalAlgHom]
  exact MvFormalGroup.algHom_apply_eq_adicEval_of_forall_apply_X_mem_radical ⊥ φ (fun i => by
    obtain ⟨n, hn⟩ := hφ i; exact ⟨n, by rw [hn]; exact Submodule.zero_mem _⟩) G

private theorem exists_coe_sub_mem_pow (G : MvPowerSeries (Fin d) (ZMod p)) (M : ℕ) :
    ∃ P : MvPolynomial (Fin d) (ZMod p), G - P ∈
      (Ideal.span (Set.range (MvPowerSeries.X : Fin d → MvPowerSeries (Fin d) (ZMod p)))) ^ M := by
  classical
  let S : Finset (Fin d →₀ ℕ) := (Finsupp.finite_of_degree_lt (σ := Fin d) M).toFinset
  refine ⟨∑ m ∈ S, MvPolynomial.monomial m (MvPowerSeries.coeff m G), ?_⟩
  refine MvPowerSeries.mem_pow_span_X_of_coeff_eq_zero M _ fun m hm => ?_
  have hmS : m ∈ S := (Set.Finite.mem_toFinset _).2 hm
  rw [map_sub, MvPolynomial.coeff_coe, MvPolynomial.coeff_sum, Finset.sum_eq_single m, MvPolynomial.coeff_monomial,
    if_pos rfl, sub_self]
  · intro m' _ hne; rw [MvPolynomial.coeff_monomial, if_neg hne]
  · intro h; exact absurd hmS h

private theorem coe_mem_pow_of_mem_pow {N : ℕ} {P : MvPolynomial (Fin d) (ZMod p)}
    (hP : P ∈ (Ideal.span (Set.range (MvPolynomial.X : Fin d → MvPolynomial (Fin d) (ZMod p)))) ^ N) :
    (P : MvPowerSeries (Fin d) (ZMod p)) ∈
      (Ideal.span (Set.range (MvPowerSeries.X : Fin d → MvPowerSeries (Fin d) (ZMod p)))) ^ N := by
  have h := Ideal.mem_map_of_mem (MvPolynomial.coeToMvPowerSeries.ringHom : MvPolynomial (Fin d) (ZMod p) →+* _) hP
  rw [Ideal.map_pow, Ideal.map_span, ← Set.range_comp] at h
  have hfun : ((MvPolynomial.coeToMvPowerSeries.ringHom : MvPolynomial (Fin d) (ZMod p) →+* _) ∘ MvPolynomial.X) =
      (MvPowerSeries.X : Fin d → MvPowerSeries (Fin d) (ZMod p)) := funext fun i => MvPolynomial.coe_X i
  rwa [hfun] at h

private theorem map_pow_X_eq_zero (φ : MvPowerSeries (Fin d) (ZMod p) →ₐ[ZMod p] A) (I : Ideal A) {M : ℕ}
    (hI : I ^ M = ⊥) (hφ : ∀ i, φ (MvPowerSeries.X i) ∈ I) {G : MvPowerSeries (Fin d) (ZMod p)}
    (hG : G ∈ (Ideal.span (Set.range (MvPowerSeries.X : Fin d → MvPowerSeries (Fin d) (ZMod p)))) ^ M) : φ G = 0 := by
  have h := Ideal.mem_map_of_mem (φ : MvPowerSeries (Fin d) (ZMod p) →+* A) hG
  rw [Ideal.map_pow, Ideal.map_span] at h
  have hle : Ideal.span ((φ : MvPowerSeries (Fin d) (ZMod p) →+* A) ''
      Set.range (MvPowerSeries.X : Fin d → MvPowerSeries (Fin d) (ZMod p))) ≤ I := by
    rw [Ideal.span_le]
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    exact hφ i
  have := Ideal.pow_right_mono hle M h
  rw [hI] at this
  exact (Submodule.mem_bot _).1 this

end PS

section Main

variable (p : ℕ) [Fact p.Prime] (h₀ : ℕ)
  (H : ℕ → Type v) [∀ v, CommRing (H v)] [∀ v, HopfAlgebra (ZMod p) (H v)]
  [∀ v, Coalgebra.IsCocomm (ZMod p) (H v)] [∀ v, Module.Finite (ZMod p) (H v)]
  (s : ∀ v, H (v + 1) →ₐc[ZMod p] H v) (hs : ∀ v, Surjective (s v))
  (hrankH : ∀ v, Module.finrank (ZMod p) (H v) = p ^ (v * h₀))
  (hkerH : ∀ v, RingHom.ker (s v) = torsionIdeal (ZMod p) (H (v + 1)) (p ^ v))
  (hlocH : ∀ v, IsLocalRing (H v))

omit [∀ v, Coalgebra.IsCocomm (ZMod p) (H v)] [∀ v, Module.Finite (ZMod p) (H v)] in

private theorem T_apply_compat (z : ∀ v, H v) (hz : ∀ v, s v (z (v + 1)) = z v) (v : ℕ) :
    ∀ w, T p H s v w (z (v + w)) = z v
  | 0 => rfl
  | w + 1 => by
    rw [T_succ, BialgHom.comp_apply]
    change T p H s v w (s (v + w) (z (v + w + 1))) = z v
    rw [hz, T_apply_compat z hz v w]

include hs hrankH hkerH hlocH in
private theorem main :
    ∃ (d : ℕ) (π : ∀ v, MvPowerSeries (Fin d) (ZMod p) →ₐ[ZMod p] H v),
      d = Module.finrank (ZMod p) (augIdeal (ZMod p) (H 1)).Cotangent ∧
      (∀ v, Surjective (π v)) ∧
      (∀ v, (s v : H (v + 1) →ₐ[ZMod p] H v).comp (π (v + 1)) = π v) ∧
      (∀ v i, Coalgebra.counit (R := ZMod p) (π v (MvPowerSeries.X i)) = 0) ∧
      (∀ v i, IsNilpotent (π v (MvPowerSeries.X i))) ∧
      (∀ N : ℕ, ∃ v, RingHom.ker (π v) ≤
        (Ideal.span (Set.range (MvPowerSeries.X : Fin d → MvPowerSeries (Fin d) (ZMod p)))) ^ N) ∧
      (∀ G, (∀ v, π v G = 0) → G = 0) ∧
      (∀ z : ∀ v, H v, (∀ v, s v (z (v + 1)) = z v) → ∃ G, ∀ v, π v G = z v) := by
  classical
  obtain ⟨d, x, hd, hxt, hxε, hsurj, hker⟩ := exists_coordinates p h₀ H s hs hrankH hkerH hlocH

  have hI : ∀ v, ∃ M : ℕ, augIdeal (ZMod p) (H v) ^ M = ⊥ := by
    intro v
    haveI := hlocH v
    haveI : IsArtinianRing (H v) := IsArtinianRing.of_finite (ZMod p) (H v)
    obtain ⟨M, hM⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := H v)
    rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top] at hM
    refine ⟨M, eq_bot_iff.2 ((Ideal.pow_right_mono (IsLocalRing.le_maximalIdeal (augIdeal_ne_top p)) M).trans hM.le)⟩
  choose M hM using hI
  have hxI : ∀ v i, x v i ∈ augIdeal (ZMod p) (H v) := fun v i => (mem_augIdeal_iff (ZMod p) (H v) _).2 (hxε v i)
  have hnil : ∀ v i, IsNilpotent (x v i) := fun v i =>
    ⟨M v, by have := Ideal.pow_mem_pow (hxI v i) (M v); rw [hM] at this; exact (Submodule.mem_bot _).1 this⟩

  let π : ∀ v, MvPowerSeries (Fin d) (ZMod p) →ₐ[ZMod p] H v := fun v => evalPS p (x v) (hnil v)
  have hπX : ∀ v i, π v (MvPowerSeries.X i) = x v i := fun v i => evalPS_X p _ _ i
  have hπcoe : ∀ v (P : MvPolynomial (Fin d) (ZMod p)), π v P = MvPolynomial.aeval (x v) P :=
    fun v P => evalPS_coe p _ _ P
  have hπpow : ∀ v G, G ∈ (Ideal.span (Set.range (MvPowerSeries.X : Fin d → MvPowerSeries (Fin d) (ZMod p)))) ^ M v →
      π v G = 0 := fun v G hG => map_pow_X_eq_zero p (π v) (augIdeal (ZMod p) (H v)) (hM v) (fun i => by rw [hπX]; exact hxI v i) hG

  have hcomp : ∀ v, (s v : H (v + 1) →ₐ[ZMod p] H v).comp (π (v + 1)) = π v := by
    intro v
    have h1 : ∀ i, IsNilpotent (((s v : H (v + 1) →ₐ[ZMod p] H v).comp (π (v + 1))) (MvPowerSeries.X i)) := by
      intro i; rw [AlgHom.comp_apply, hπX]; change IsNilpotent (s v (x (v + 1) i)); rw [hxt]; exact hnil v i
    rw [eq_evalPS p _ h1, eq_evalPS p (π v) (fun i => by rw [hπX]; exact hnil v i)]
    congr 1
    funext i
    rw [AlgHom.comp_apply, hπX, hπX]
    exact hxt v i
  have hcompT : ∀ v w, ((T p H s v w : H (v + w) →ₐc[ZMod p] H v) : H (v + w) →ₐ[ZMod p] H v).comp (π (v + w)) = π v := by
    intro v w
    induction w with
    | zero => rfl
    | succ w ih => rw [T_succ, ← ih, ← hcomp (v + w)]; rfl

  have hkerPS : ∀ N : ℕ, ∃ v, RingHom.ker (π v) ≤
      (Ideal.span (Set.range (MvPowerSeries.X : Fin d → MvPowerSeries (Fin d) (ZMod p)))) ^ N := by
    intro N
    obtain ⟨v, hv⟩ := hker N
    refine ⟨v, fun G hG => ?_⟩
    obtain ⟨P, hP⟩ := exists_coe_sub_mem_pow p G (max N (M v))
    have hP' : π v (G - P) = 0 := hπpow v _ (Ideal.pow_le_pow_right (le_max_right _ _) hP)
    rw [RingHom.mem_ker] at hG
    rw [map_sub, hG, zero_sub, neg_eq_zero, hπcoe] at hP'
    have h1 : (P : MvPowerSeries (Fin d) (ZMod p)) ∈ (Ideal.span (Set.range (MvPowerSeries.X : Fin d → _))) ^ N :=
      coe_mem_pow_of_mem_pow p (hv (by rwa [RingHom.mem_ker]))
    have h2 := Ideal.pow_le_pow_right (le_max_left N (M v)) hP
    have : G = (G - P) + P := by ring
    rw [this]
    exact Ideal.add_mem _ h2 h1

  have hkermono : ∀ v w, RingHom.ker (π (v + w)) ≤ RingHom.ker (π v) := by
    intro v w G hG
    rw [RingHom.mem_ker] at hG ⊢
    rw [← hcompT v w, AlgHom.comp_apply, hG, map_zero]
  refine ⟨d, π, hd, fun v => ?_, hcomp, fun v i => by rw [hπX]; exact hxε v i, fun v i => by rw [hπX]; exact hnil v i,
    hkerPS, fun G hG => ?_, fun z hz => ?_⟩
  ·
    intro a
    obtain ⟨P, rfl⟩ := hsurj v a
    exact ⟨P, hπcoe v P⟩
  ·
    ext m
    obtain ⟨v, hv⟩ := hkerPS (m.degree + 1)
    rw [map_zero]
    exact coeff_eq_zero_of_mem_pow p (hv (by rw [RingHom.mem_ker]; exact hG v)) (Nat.lt_succ_self _)
  ·
    choose v₀ hv₀ using hkerPS
    let lev : ℕ → ℕ := fun N => Nat.rec (motive := fun _ => ℕ) (v₀ 0) (fun N l => max (max l (v₀ (N + 1))) (N + 1)) N
    have lev_succ : ∀ N, lev (N + 1) = max (max (lev N) (v₀ (N + 1))) (N + 1) := fun N => rfl
    have hlevker : ∀ N, RingHom.ker (π (lev N)) ≤
        (Ideal.span (Set.range (MvPowerSeries.X : Fin d → MvPowerSeries (Fin d) (ZMod p)))) ^ N := by
      intro N
      cases N with
      | zero => exact hv₀ 0
      | succ N =>
        obtain ⟨w, hw⟩ := Nat.exists_eq_add_of_le (show v₀ (N + 1) ≤ lev (N + 1) by rw [lev_succ]; omega)
        rw [hw]
        exact (hkermono _ w).trans (hv₀ (N + 1))
    have hlevmono : ∀ N N', N ≤ N' → lev N ≤ lev N' := by
      intro N N' h
      induction h with
      | refl => exact le_rfl
      | step _ ih => rw [lev_succ]; omega
    have hlevge : ∀ N, N ≤ lev N := by
      intro N; cases N with
      | zero => exact Nat.zero_le _
      | succ N => rw [lev_succ]; omega

    have hlift : ∀ N, ∃ P : MvPolynomial (Fin d) (ZMod p), π (lev N) P = z (lev N) := by
      intro N
      obtain ⟨P, hP⟩ := hsurj (lev N) (z (lev N))
      exact ⟨P, by rw [hπcoe, hP]⟩
    choose P hP using hlift

    have hagree : ∀ N N', N ≤ N' → ∀ m : Fin d →₀ ℕ, m.degree < N →
        MvPolynomial.coeff m (P N) = MvPolynomial.coeff m (P N') := by
      intro N N' hNN' m hm
      obtain ⟨w, hw⟩ := Nat.exists_eq_add_of_le (hlevmono N N' hNN')
      have h1 : π (lev N) (P N') = z (lev N) := by
        have h2 := hP N'
        rw [hw] at h2
        rw [← hcompT (lev N) w, AlgHom.comp_apply, h2]
        exact T_apply_compat p H s z hz (lev N) w
      have h3 : ((P N : MvPolynomial (Fin d) (ZMod p)) : MvPowerSeries (Fin d) (ZMod p)) - P N' ∈ RingHom.ker (π (lev N)) := by
        rw [RingHom.mem_ker, map_sub, hP N, h1, sub_self]
      have h4 := coeff_eq_zero_of_mem_pow p (hlevker N h3) hm
      rwa [map_sub, MvPolynomial.coeff_coe, MvPolynomial.coeff_coe, sub_eq_zero] at h4

    let G : MvPowerSeries (Fin d) (ZMod p) := fun m => MvPolynomial.coeff m (P (m.degree + 1))
    have hGcoeff : ∀ m, MvPowerSeries.coeff m G = MvPolynomial.coeff m (P (m.degree + 1)) := fun m => rfl
    have hGP : ∀ N, G - P N ∈ (Ideal.span (Set.range (MvPowerSeries.X : Fin d → MvPowerSeries (Fin d) (ZMod p)))) ^ N := by
      intro N
      refine MvPowerSeries.mem_pow_span_X_of_coeff_eq_zero N _ fun m hm => ?_
      rw [map_sub, hGcoeff, MvPolynomial.coeff_coe, sub_eq_zero]
      rcases le_total (m.degree + 1) N with h | h
      · exact hagree _ _ h m (Nat.lt_succ_self _)
      · exact (hagree _ _ h m hm).symm
    refine ⟨G, fun v => ?_⟩

    set N := max v (M v) with hN
    obtain ⟨w, hw⟩ := Nat.exists_eq_add_of_le ((le_max_left v (M v)).trans (hlevge N))
    have h1 : π v (G - P N) = 0 := hπpow v _ (Ideal.pow_le_pow_right (le_max_right v (M v)) (hGP N))
    rw [map_sub, sub_eq_zero] at h1
    rw [h1, ← hcompT v w, AlgHom.comp_apply]
    have h2 := hP N
    rw [hw] at h2
    rw [h2]
    exact T_apply_compat p H s z hz v w

end Main

end CoordField

open CoordField MvPowerSeries in
theorem solution
    (p : ℕ) [Fact p.Prime] (h₀ : ℕ)
    (H : ℕ → Type v) [∀ v, CommRing (H v)] [∀ v, HopfAlgebra (ZMod p) (H v)]
    [∀ v, Coalgebra.IsCocomm (ZMod p) (H v)] [∀ v, Module.Finite (ZMod p) (H v)]
    (s : ∀ v, H (v + 1) →ₐc[ZMod p] H v) (hs : ∀ v, Function.Surjective (s v))
    (hrankH : ∀ v, Module.finrank (ZMod p) (H v) = p ^ (v * h₀))
    (hkerH : ∀ v, RingHom.ker (s v) = PDivisibleGroup.Hopf.torsionIdeal (ZMod p) (H (v + 1)) (p ^ v))
    (hlocH : ∀ v, IsLocalRing (H v)) :
    ∃ (d : ℕ) (π : ∀ v, MvPowerSeries (Fin d) (ZMod p) →ₐ[ZMod p] H v),
      d = Module.finrank (ZMod p) (PDivisibleGroup.Hopf.augIdeal (ZMod p) (H 1)).Cotangent ∧
      (∀ v, Function.Surjective (π v)) ∧
      (∀ v, (s v : H (v + 1) →ₐ[ZMod p] H v).comp (π (v + 1)) = π v) ∧
      (∀ v i, Coalgebra.counit (R := ZMod p) (π v (X i)) = 0) ∧
      (∀ v i, IsNilpotent (π v (X i))) ∧
      (∀ N : ℕ, ∃ v, RingHom.ker (π v) ≤
        (Ideal.span (Set.range (X : Fin d → MvPowerSeries (Fin d) (ZMod p)))) ^ N) ∧
      (∀ G, (∀ v, π v G = 0) → G = 0) ∧
      (∀ z : ∀ v, H v, (∀ v, s v (z (v + 1)) = z v) → ∃ G, ∀ v, π v G = z v) := by
  exact main p h₀ H s hs hrankH hkerH hlocH

end S_PDivisibleGroup_exists_surjective_mvPowerSeries_comp_eq_of_isLocalRing_zmodp
end P2MW
export P2MW.S_PDivisibleGroup_exists_surjective_mvPowerSeries_comp_eq_of_isLocalRing_zmodp (solution)
