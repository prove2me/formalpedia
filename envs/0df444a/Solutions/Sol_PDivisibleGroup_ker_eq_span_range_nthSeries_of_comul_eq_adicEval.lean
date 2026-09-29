-- Prove2me | solution 1 for PDivisibleGroup.ker_eq_span_range_nthSeries_of_comul_eq_adicEval
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/405387dc-559b-5f50-8e2e-c946b6b86190

import Mathlib
import Definitions.Def_PDivisibleGroup_Basic
import Definitions.Def_MvFormalGroup_BasicV2
import Definitions.Def_MvFormalGroup_PointsV2
import Theorems.Thm_MvFormalGroup_algHom_apply_eq_adicEval_of_forall_apply_X_mem_radical
import Theorems.Thm_IsLocalRing_exists_le_maximalIdeal_pow_of_iInf_eq_bot_of_isAdicComplete
import Theorems.Thm_PDivisibleGroup_Hopf_exists_forall_comp_transition_surjective_ker_eq_torsionIdeal
import Theorems.Thm_IsAdicComplete_of_module_finite_free_span_natCast
import Theorems.Thm_MvPowerSeries_isNoetherianRing_of_finite
import Theorems.Thm_MvPowerSeries_isAdicComplete_maximalIdeal
import Theorems.Thm_IsAdicComplete_exists_isDomain_isDiscreteValuationRing_of_ker_algebraMap_zmod_eq_span
import Theorems.Thm_MvPowerSeries_mem_pow_span_X_of_coeff_eq_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PDivisibleGroup_ker_eq_span_range_nthSeries_of_comul_eq_adicEval

set_option autoImplicit false

open MvPowerSeries
open scoped TensorProduct

universe u v

namespace TorsionLevel

private theorem isAdicComplete_span_natCast_of_free {𝓞 : Type u} [CommRing 𝓞] (p : ℕ)
    [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞]
    (S : Type v) [CommRing S] [Algebra 𝓞 S] [Module.Free 𝓞 S] [Module.Finite 𝓞 S] :
    IsAdicComplete (Ideal.span {(p : S)}) S :=
  IsAdicComplete.of_module_finite_free_span_natCast (𝓞 := 𝓞) p S

private theorem psComplete {𝓞 : Type u} [CommRing 𝓞] [IsNoetherianRing 𝓞] [IsLocalRing 𝓞]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝓞) 𝓞] (d : ℕ) :
    ∃ (_ : IsNoetherianRing (MvPowerSeries (Fin d) 𝓞)) (_ : IsLocalRing (MvPowerSeries (Fin d) 𝓞)),
      IsAdicComplete (IsLocalRing.maximalIdeal (MvPowerSeries (Fin d) 𝓞)) (MvPowerSeries (Fin d) 𝓞) :=
  ⟨MvPowerSeries.isNoetherianRing_of_finite, inferInstance, MvPowerSeries.isAdicComplete_maximalIdeal⟩

private theorem obase {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    [Algebra 𝓞 (ZMod p)] (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)})
    [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞] :
    ∃ (_ : IsNoetherianRing 𝓞) (_ : IsLocalRing 𝓞), IsLocalRing.maximalIdeal 𝓞 = Ideal.span {(p : 𝓞)} := by
  obtain ⟨_, _, -, hmax⟩ :=
    IsAdicComplete.exists_isDomain_isDiscreteValuationRing_of_ker_algebraMap_zmod_eq_span p hp hker
  exact ⟨inferInstance, inferInstance, hmax⟩

section Level

variable {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime]
variable (R : Type v) [CommRing R] [HopfAlgebra 𝓞 R]
variable [IsAdicComplete (Ideal.span {(p : R)}) R] [IsAdicComplete (Ideal.span {(p : R ⊗[𝓞] R)}) (R ⊗[𝓞] R)]
variable {d : ℕ} (π : MvPowerSeries (Fin d) 𝓞 →ₐ[𝓞] R)
variable (hπX : ∀ i, π (X i) ∈ (Ideal.span {(p : R)}).radical)
variable (F : MvFormalGroup d 𝓞)
variable (hπΔ : ∀ i, Coalgebra.comul (R := 𝓞) (π (X i)) =
  MvFormalGroup.adicEval (Ideal.span {(p : R ⊗[𝓞] R)})
    (Sum.elim (fun j => π (X j) ⊗ₜ[𝓞] (1 : R)) (fun j => (1 : R) ⊗ₜ[𝓞] π (X j))) (F.toPowerSeries i))

omit [Fact p.Prime] [IsAdicComplete (Ideal.span {(p : R)}) R]
  [IsAdicComplete (Ideal.span {(p : R ⊗[𝓞] R)}) (R ⊗[𝓞] R)] in

private theorem map_mem_radical {B C : Type*} [CommRing B] [Algebra 𝓞 B] [CommRing C] [Algebra 𝓞 C]
    (f : B →ₐ[𝓞] C) {b : B} (hb : b ∈ (Ideal.span {(p : B)}).radical) :
    f b ∈ (Ideal.span {(p : C)}).radical := by
  obtain ⟨n, hn⟩ := hb
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hn
  refine ⟨n, ?_⟩
  rw [← map_pow, ← hc, map_mul, map_natCast]
  exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)

private theorem constantCoeff_nthSeries (F : MvFormalGroup d 𝓞) : ∀ (n : ℕ) (j : Fin d),
    MvPowerSeries.constantCoeff (F.nthSeries n j) = 0
  | 0, j => by rw [MvFormalGroup.nthSeries_zero, map_zero]
  | n + 1, j => by
    rw [MvFormalGroup.nthSeries_succ]
    refine constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero ?_) ?_ (F.constantCoeff_eq_zero j)
    · rintro (l | l)
      · exact constantCoeff_nthSeries F n l
      · exact constantCoeff_X l
    · rintro (l | l)
      · exact constantCoeff_nthSeries F n l
      · exact constantCoeff_X l

private theorem hasSubst_nthSeries (F : MvFormalGroup d 𝓞) (n : ℕ) :
    HasSubst (Sum.elim (F.nthSeries n) fun j => (X j : MvPowerSeries (Fin d) 𝓞)) :=
  hasSubst_of_constantCoeff_zero (by
    rintro (l | l)
    · exact constantCoeff_nthSeries F n l
    · exact constantCoeff_X l)

include hπX in
omit [Fact p.Prime] [IsAdicComplete (Ideal.span {(p : R ⊗[𝓞] R)}) (R ⊗[𝓞] R)] in

private theorem apply_eq_adicEval (G : MvPowerSeries (Fin d) 𝓞) :
    π G = MvFormalGroup.adicEval (Ideal.span {(p : R)}) (fun j => π (X j)) G :=
  MvFormalGroup.algHom_apply_eq_adicEval_of_forall_apply_X_mem_radical _ π hπX G

private theorem nsmulAlgHom_succ_apply (n : ℕ) (a : R) :
    PDivisibleGroup.Hopf.nsmulAlgHom 𝓞 R (n + 1) a =
      ((Algebra.TensorProduct.lmul' 𝓞 (S := R)).comp
        (Algebra.TensorProduct.map (PDivisibleGroup.Hopf.nsmulAlgHom 𝓞 R n) (AlgHom.id 𝓞 R)))
        (Coalgebra.comul (R := 𝓞) a) := by
  have h1 : PDivisibleGroup.Hopf.nsmulAlgHom 𝓞 R (n + 1) a =
      LinearMap.mul' 𝓞 R (TensorProduct.map (PDivisibleGroup.Hopf.nsmulAlgHom 𝓞 R n).toLinearMap
        LinearMap.id (Coalgebra.comul (R := 𝓞) a)) := by
    have h := PDivisibleGroup.Hopf.toLinearMap_nsmulAlgHom 𝓞 R (n + 1)
    rw [pow_succ] at h
    have h' := LinearMap.congr_fun h a
    rw [AlgHom.toLinearMap_apply] at h'
    rw [h', LinearMap.convMul_apply, ← PDivisibleGroup.Hopf.toLinearMap_nsmulAlgHom, WithConv.ofConv_toConv]
  rw [h1]
  generalize Coalgebra.comul (R := 𝓞) a = z
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul x y =>
    rw [TensorProduct.map_tmul, LinearMap.mul'_apply, AlgHom.comp_apply, Algebra.TensorProduct.map_tmul,
      Algebra.TensorProduct.lmul'_apply_tmul]
    rfl
  | add x y hx hy => simp only [map_add, hx, hy]

include hπX hπΔ in
omit [Fact p.Prime] in

private theorem apply_nthSeries_eq_nsmulAlgHom (hπε : ∀ i, Coalgebra.counit (R := 𝓞) (π (X i)) = 0) :
    ∀ (n : ℕ) (i : Fin d), π (F.nthSeries n i) = PDivisibleGroup.Hopf.nsmulAlgHom 𝓞 R n (π (X i))
  | 0, i => by
    rw [MvFormalGroup.nthSeries_zero, map_zero, PDivisibleGroup.Hopf.nsmulAlgHom_zero_apply, hπε, map_zero]
  | n + 1, i => by

    set Ψ : R ⊗[𝓞] R →ₐ[𝓞] R := (Algebra.TensorProduct.lmul' 𝓞 (S := R)).comp
      (Algebra.TensorProduct.map (PDivisibleGroup.Hopf.nsmulAlgHom 𝓞 R n) (AlgHom.id 𝓞 R)) with hΨ
    have hR : PDivisibleGroup.Hopf.nsmulAlgHom 𝓞 R (n + 1) (π (X i)) =
        MvFormalGroup.adicEval (Ideal.span {(p : R)})
          (Sum.elim (fun j => π (F.nthSeries n j)) (fun j => π (X j))) (F.toPowerSeries i) := by
      rw [nsmulAlgHom_succ_apply, hπΔ, ← hΨ,
        MvFormalGroup.map_adicEval (R := 𝓞) (Ideal.span {(p : R ⊗[𝓞] R)}) (Ideal.span {(p : R)}) Ψ
          (Submodule.fg_span_singleton _) ?_ ?_ (F.toPowerSeries i)]
      · congr 1
        funext s
        rcases s with j | j
        · rw [Sum.elim_inl, Sum.elim_inl, hΨ, AlgHom.comp_apply, Algebra.TensorProduct.map_tmul,
            AlgHom.id_apply, Algebra.TensorProduct.lmul'_apply_tmul, mul_one,
            apply_nthSeries_eq_nsmulAlgHom hπε n j]
        · rw [Sum.elim_inr, Sum.elim_inr, hΨ, AlgHom.comp_apply, Algebra.TensorProduct.map_tmul,
            AlgHom.id_apply, Algebra.TensorProduct.lmul'_apply_tmul, map_one, one_mul]
      · intro s hs
        obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hs
        refine Ideal.le_radical ?_
        rw [map_mul, map_natCast]
        exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
      · rintro (j | j)
        · rw [Sum.elim_inl]
          exact map_mem_radical p (Algebra.TensorProduct.includeLeft : R →ₐ[𝓞] R ⊗[𝓞] R) (hπX j)
        · rw [Sum.elim_inr]
          exact map_mem_radical p (Algebra.TensorProduct.includeRight : R →ₐ[𝓞] R ⊗[𝓞] R) (hπX j)

    have hL : π (F.nthSeries (n + 1) i) =
        MvFormalGroup.adicEval (Ideal.span {(p : R)})
          (Sum.elim (fun j => π (F.nthSeries n j)) (fun j => π (X j))) (F.toPowerSeries i) := by
      rw [MvFormalGroup.nthSeries_succ, apply_eq_adicEval p R π hπX,
        MvFormalGroup.adicEval_subst (R := 𝓞) (Ideal.span {(p : R)}) (fun j => hπX j) (hasSubst_nthSeries F n)]
      congr 1
      funext s
      rcases s with j | j
      · rw [Sum.elim_inl, Sum.elim_inl, apply_eq_adicEval p R π hπX]
      · rw [Sum.elim_inr, Sum.elim_inr, MvFormalGroup.adicEval_X]
    rw [hL, hR]

omit [Fact p.Prime] [IsAdicComplete (Ideal.span {(p : R)}) R]
  [IsAdicComplete (Ideal.span {(p : R ⊗[𝓞] R)}) (R ⊗[𝓞] R)] in

private theorem counit_apply_eq_constantCoeff (G : MvPowerSeries (Fin d) 𝓞)
    (hπε : ∀ i, Coalgebra.counit (R := 𝓞) (π (X i)) = 0) :
    Coalgebra.counit (R := 𝓞) (π G) = MvPowerSeries.constantCoeff G := by
  let κ : MvPowerSeries (Fin d) 𝓞 →ₐ[𝓞] 𝓞 :=
    { MvPowerSeries.constantCoeff with commutes' := fun c => MvPowerSeries.constantCoeff_C c }
  have h1 := MvFormalGroup.algHom_apply_eq_adicEval_of_forall_apply_X_mem_radical (⊥ : Ideal 𝓞)
    ((Bialgebra.counitAlgHom 𝓞 R).comp π) (fun s => by
      rw [AlgHom.comp_apply, Bialgebra.counitAlgHom_apply, hπε]; exact Ideal.zero_mem _) G
  have h2 := MvFormalGroup.algHom_apply_eq_adicEval_of_forall_apply_X_mem_radical (⊥ : Ideal 𝓞) κ
    (fun s => by
      change MvPowerSeries.constantCoeff (X s) ∈ _
      rw [constantCoeff_X]; exact Ideal.zero_mem _) G
  rw [AlgHom.comp_apply, Bialgebra.counitAlgHom_apply] at h1
  rw [h1]
  change _ = κ G
  rw [h2]
  congr 1
  funext s
  rw [AlgHom.comp_apply, Bialgebra.counitAlgHom_apply, hπε]
  change (0 : 𝓞) = MvPowerSeries.constantCoeff (X s)
  rw [constantCoeff_X]

include hπX hπΔ in
omit [Fact p.Prime] in

private theorem torsionIdeal_eq_map_span_nthSeries (hπ : Function.Surjective π)
    (hπε : ∀ i, Coalgebra.counit (R := 𝓞) (π (X i)) = 0) (n : ℕ) :
    PDivisibleGroup.Hopf.torsionIdeal 𝓞 R n =
      Ideal.map π (Ideal.span (Set.range (F.nthSeries n))) := by

  have haug : PDivisibleGroup.Hopf.augIdeal 𝓞 R =
      Ideal.map π (Ideal.span (Set.range (X : Fin d → MvPowerSeries (Fin d) 𝓞))) := by
    apply le_antisymm
    · intro a ha
      obtain ⟨G, rfl⟩ := hπ a
      rw [PDivisibleGroup.Hopf.mem_augIdeal_iff, counit_apply_eq_constantCoeff R π G hπε] at ha
      refine Ideal.mem_map_of_mem _ ?_
      have := MvPowerSeries.mem_pow_span_X_of_coeff_eq_zero 1 G (fun m hm => by
        have hm0 : m = 0 := (Finsupp.degree_eq_zero_iff m).1 (by omega)
        rw [hm0, MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
        exact ha)
      rwa [pow_one] at this
    · rw [Ideal.map_span, Ideal.span_le]
      rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
      exact (PDivisibleGroup.Hopf.mem_augIdeal_iff 𝓞 R _).2 (hπε i)
  rw [PDivisibleGroup.Hopf.torsionIdeal, haug, Ideal.map_span, Ideal.map_span, Ideal.map_span, Set.image_image,
    ← Set.range_comp, ← Set.range_comp]
  congr 2
  funext i
  exact (apply_nthSeries_eq_nsmulAlgHom p R π hπX F hπΔ hπε n i).symm

end Level

end TorsionLevel

open TorsionLevel in
theorem solution
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    [Algebra 𝓞 (ZMod p)] (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)})
    [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞]
    (h₀ : ℕ) (R₀ : ℕ → Type v) [∀ v, CommRing (R₀ v)] [∀ v, HopfAlgebra 𝓞 (R₀ v)]
    [∀ v, Coalgebra.IsCocomm 𝓞 (R₀ v)] [∀ v, Module.Free 𝓞 (R₀ v)] [∀ v, Module.Finite 𝓞 (R₀ v)]
    (t₀ : ∀ v, R₀ (v + 1) →ₐc[𝓞] R₀ v) (ht₀ : ∀ v, Function.Surjective (t₀ v))
    (hrank₀ : ∀ v, Module.finrank 𝓞 (R₀ v) = p ^ (v * h₀))
    (hker₀ : ∀ v, RingHom.ker (t₀ v) = PDivisibleGroup.Hopf.torsionIdeal 𝓞 (R₀ (v + 1)) (p ^ v))
    (hconn : ∀ v, IsLocalRing (R₀ v))
    (d : ℕ) (π : ∀ v, MvPowerSeries (Fin d) 𝓞 →ₐ[𝓞] R₀ v)
    (hπ : ∀ v, Function.Surjective (π v))
    (hπt : ∀ v, (t₀ v : R₀ (v + 1) →ₐ[𝓞] R₀ v).comp (π (v + 1)) = π v)
    (hπε : ∀ v i, Coalgebra.counit (R := 𝓞) (π v (X i)) = 0)
    (hπX : ∀ v i, π v (X i) ∈ (Ideal.span {(p : R₀ v)}).radical)
    (hπinj : ∀ G, (∀ v, π v G = 0) → G = 0)
    (hπsurjj : ∀ z : ∀ v, R₀ v, (∀ v, t₀ v (z (v + 1)) = z v) → ∃ G, ∀ v, π v G = z v)
    (F : MvFormalGroup d 𝓞)
    (hπΔ : ∀ v i, Coalgebra.comul (R := 𝓞) (π v (X i)) =
      MvFormalGroup.adicEval (Ideal.span {(p : R₀ v ⊗[𝓞] R₀ v)})
        (Sum.elim (fun j => π v (X j) ⊗ₜ[𝓞] (1 : R₀ v)) (fun j => (1 : R₀ v) ⊗ₜ[𝓞] π v (X j)))
        (F.toPowerSeries i))
    (v : ℕ) :
    RingHom.ker (π v) = Ideal.span (Set.range (F.nthSeries (p ^ v))) := by
  classical

  obtain ⟨instN, instL, hmax⟩ := TorsionLevel.obase p hp hker
  haveI : ∀ w, IsAdicComplete (Ideal.span {(p : R₀ w)}) (R₀ w) := fun w =>
    TorsionLevel.isAdicComplete_span_natCast_of_free (𝓞 := 𝓞) p (R₀ w)
  haveI : ∀ w, IsAdicComplete (Ideal.span {(p : R₀ w ⊗[𝓞] R₀ w)}) (R₀ w ⊗[𝓞] R₀ w) := fun w =>
    TorsionLevel.isAdicComplete_span_natCast_of_free (𝓞 := 𝓞) p (R₀ w ⊗[𝓞] R₀ w)
  haveI : IsAdicComplete (IsLocalRing.maximalIdeal 𝓞) 𝓞 := by rw [hmax]; infer_instance
  obtain ⟨instNA, instLA, instCA⟩ := TorsionLevel.psComplete (𝓞 := 𝓞) d
  set A := MvPowerSeries (Fin d) 𝓞 with hA
  set J : Ideal A := Ideal.span (Set.range (F.nthSeries (p ^ v))) with hJ

  obtain ⟨T, hT0, hTsucc, hTsurj, hTker, hpv, -⟩ :=
    PDivisibleGroup.Hopf.exists_forall_comp_transition_surjective_ker_eq_torsionIdeal p h₀ R₀ t₀ ht₀ hrank₀ hker₀
  apply le_antisymm
  ·

    have hanti : Antitone fun w => RingHom.ker (π w) := by
      refine antitone_nat_of_succ_le fun w => ?_
      intro G hG
      rw [RingHom.mem_ker] at hG ⊢
      rw [← hπt w, AlgHom.comp_apply, hG, map_zero]
    have hinf : ⨅ w, RingHom.ker (π w) = ⊥ := by
      refine eq_bot_iff.2 fun G hG => ?_
      rw [Ideal.mem_bot]
      exact hπinj G fun w => by
        have := (Ideal.mem_iInf.1 hG) w
        rwa [RingHom.mem_ker] at this

    have hTπ : ∀ w, ((T v w : R₀ (v + w) →ₐc[𝓞] R₀ v) : R₀ (v + w) →ₐ[𝓞] R₀ v).comp (π (v + w)) = π v := by
      intro w
      induction w with
      | zero => rw [hT0]; rfl
      | succ w ih =>
        rw [hTsucc, ← ih, ← hπt (v + w)]
        rfl
    have hkv : ∀ w, RingHom.ker (π v) = J ⊔ RingHom.ker (π (v + w)) := by
      intro w
      have h1 : RingHom.ker (π v) = Ideal.comap (π (v + w)) (RingHom.ker (T v w : R₀ (v + w) →ₐc[𝓞] R₀ v)) := by
        rw [← hTπ w]
        ext G
        simp only [RingHom.mem_ker, Ideal.mem_comap, AlgHom.comp_apply]
        rfl
      rw [h1, hTker, TorsionLevel.torsionIdeal_eq_map_span_nthSeries p (R₀ (v + w)) (π (v + w))
        (hπX (v + w)) F (hπΔ (v + w)) (hπ (v + w)) (hπε (v + w)) (p ^ v),
        Ideal.comap_map_of_surjective _ (hπ (v + w)), ← RingHom.ker_eq_comap_bot]

    intro G hG
    have hGN : ∀ N : ℕ, G ∈ J ⊔ IsLocalRing.maximalIdeal A ^ N := by
      intro N
      obtain ⟨w, hw⟩ := IsLocalRing.exists_le_maximalIdeal_pow_of_iInf_eq_bot_of_isAdicComplete
        (fun w => RingHom.ker (π w)) hanti hinf N
      have hG' : G ∈ RingHom.ker (π v) := hG
      rw [hkv w] at hG'
      have hle : RingHom.ker (π (v + w)) ≤ IsLocalRing.maximalIdeal A ^ N :=
        le_trans (hanti (Nat.le_add_left w v)) hw
      exact (sup_le_sup_left hle J) hG'

    have hKrull : (⨅ N : ℕ, J ⊔ IsLocalRing.maximalIdeal A ^ N) = J := by
      refine le_antisymm ?_ (le_iInf fun N => le_sup_left)
      intro G hG
      have hbot := Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (M := A ⧸ J)
        (I := IsLocalRing.maximalIdeal A) (IsLocalRing.maximalIdeal.isMaximal A).ne_top
      have hmk : J.mkQ G ∈ (⨅ N : ℕ, IsLocalRing.maximalIdeal A ^ N • (⊤ : Submodule A (A ⧸ J))) := by
        refine (Submodule.mem_iInf _).2 fun N => ?_
        obtain ⟨j, hj, m, hm, rfl⟩ := Submodule.mem_sup.1 ((Submodule.mem_iInf _).1 hG N)
        have hj0 : J.mkQ j = 0 := (Submodule.Quotient.mk_eq_zero J).2 hj
        rw [map_add, hj0, zero_add]
        have hm' : m ∈ IsLocalRing.maximalIdeal A ^ N • (⊤ : Submodule A A) := by
          simpa only [smul_eq_mul, mul_one] using
            Submodule.smul_mem_smul hm (Submodule.mem_top : (1 : A) ∈ (⊤ : Submodule A A))
        have h2 := Submodule.mem_map_of_mem (f := J.mkQ) hm'
        rwa [Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ] at h2
      rw [hbot, Submodule.mem_bot, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hmk
      exact hmk
    rw [← hKrull]
    exact Ideal.mem_iInf.2 hGN
  ·
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, RingHom.mem_ker]
    change π v (F.nthSeries (p ^ v) i) = 0
    rw [TorsionLevel.apply_nthSeries_eq_nsmulAlgHom p (R₀ v) (π v) (hπX v) F (hπΔ v) (hπε v), hpv v,
      AlgHom.comp_apply, Bialgebra.counitAlgHom_apply, hπε, map_zero]

end S_PDivisibleGroup_ker_eq_span_range_nthSeries_of_comul_eq_adicEval
end P2MW
export P2MW.S_PDivisibleGroup_ker_eq_span_range_nthSeries_of_comul_eq_adicEval (solution)
