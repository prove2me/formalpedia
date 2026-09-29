-- Prove2me | solution 1 for PDivisibleGroup.exists_tower_isLocalRing_isReduced_bijective_tensorProduct_comul_zmodp
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/cfc072b0-268a-5c2d-808c-bcaed26d6322

import Mathlib
import Definitions.Def_PDivisibleGroup_Basic
import Theorems.Thm_HopfAlgebra_exists_isLocalRing_isReduced_bijective_tensorProduct_comul_zmodp
import Theorems.Thm_HopfAlgebra_finrank_eq_finrank_quotient_map_ker_counit_mul_finrank_range
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PDivisibleGroup_exists_tower_isLocalRing_isReduced_bijective_tensorProduct_comul_zmodp
p2m_attr_erase "instance" "HopfAlgebra.HopfIdealQuotient.instIsCocomm HopfAlgebra.HopfIdealQuotient.instBialgebra HopfAlgebra.HopfIdealQuotient.instHopfAlgebra Ideal.isHopfIdeal_bot HopfAlgebra.flat_quotient_bot HopfAlgebra.finiteType_quotient HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra"
p2m_attr_erase "simp" "HopfAlgebra.HopfIdealQuotient.comul_mk HopfAlgebra.antipodeAlgHom_apply HopfAlgebra.quotientFactorBialgHom_apply_mk HopfAlgebra.quotientBialgHom_apply HopfAlgebra.quotientLiftPoint_mk HopfAlgebra.convCompMonoidHom_apply HopfAlgebra.HopfIdealQuotient.antipode_mk HopfAlgebra.HopfIdealQuotient.counit_mk HopfAlgebra.canAlgHom_tmul HopfAlgebra.canMap_tmul HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul"

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000
set_option Elab.async false

open scoped TensorProduct
open Coalgebra Bialgebra

universe u v w

noncomputable section

namespace S42Tower

section Descend

variable {R : Type*} [CommRing R]
  {A : Type*} [CommRing A] [Bialgebra R A]
  {B : Type*} [CommRing B] [Bialgebra R B]
  {C : Type*} [CommRing C] [Bialgebra R C]

theorem algHom_eq_of_comp_eq {D : Type*} [Semiring D] [Algebra R D] {π : A →ₐ[R] B}
    (hπ : Function.Surjective π) {f g : B →ₐ[R] D} (h : f.comp π = g.comp π) : f = g := by
  refine AlgHom.ext fun b => ?_
  obtain ⟨a, rfl⟩ := hπ b
  exact AlgHom.congr_fun h a

def descendAlgHom (π : A →ₐ[R] B) (hπ : Function.Surjective π) (g : A →ₐ[R] C)
    (h : ∀ a, π a = 0 → g a = 0) : B →ₐ[R] C :=
  (Ideal.Quotient.liftₐ (RingHom.ker π) g (fun a ha => h a ha)).comp
    (Ideal.quotientKerAlgEquivOfSurjective hπ).symm.toAlgHom

theorem descendAlgHom_apply (π : A →ₐ[R] B) (hπ : Function.Surjective π) (g : A →ₐ[R] C)
    (h : ∀ a, π a = 0 → g a = 0) (a : A) : descendAlgHom π hπ g h (π a) = g a := by
  have hq : (Ideal.quotientKerAlgEquivOfSurjective hπ).symm (π a) = Ideal.Quotient.mk (RingHom.ker π) a :=
    (Ideal.quotientKerAlgEquivOfSurjective hπ).injective (by simp)
  change Ideal.Quotient.liftₐ (RingHom.ker π) g (fun a ha => h a ha)
    ((Ideal.quotientKerAlgEquivOfSurjective hπ).symm (π a)) = g a
  rw [hq]
  rfl

theorem descendAlgHom_comp (π : A →ₐ[R] B) (hπ : Function.Surjective π) (g : A →ₐ[R] C)
    (h : ∀ a, π a = 0 → g a = 0) : (descendAlgHom π hπ g h).comp π = g :=
  AlgHom.ext (descendAlgHom_apply π hπ g h)

def descend (π : A →ₐc[R] B) (hπ : Function.Surjective π) (g : A →ₐc[R] C)
    (h : ∀ a, π a = 0 → g a = 0) : B →ₐc[R] C :=
  BialgHom.ofAlgHom (descendAlgHom (π : A →ₐ[R] B) hπ (g : A →ₐ[R] C) h)
    (by
      apply algHom_eq_of_comp_eq (π := (π : A →ₐ[R] B)) hπ
      rw [AlgHom.comp_assoc, descendAlgHom_comp, BialgHom.counitAlgHom_comp,
        BialgHom.counitAlgHom_comp])
    (by
      apply algHom_eq_of_comp_eq (π := (π : A →ₐ[R] B)) hπ
      rw [AlgHom.comp_assoc, ← BialgHom.map_comp_comulAlgHom, ← AlgHom.comp_assoc,
        ← Algebra.TensorProduct.map_comp, descendAlgHom_comp, BialgHom.map_comp_comulAlgHom,
        AlgHom.comp_assoc, descendAlgHom_comp])

theorem descend_apply (π : A →ₐc[R] B) (hπ : Function.Surjective π) (g : A →ₐc[R] C)
    (h : ∀ a, π a = 0 → g a = 0) (a : A) : descend π hπ g h (π a) = g a :=
  descendAlgHom_apply (π : A →ₐ[R] B) hπ (g : A →ₐ[R] C) h a

theorem descend_comp (π : A →ₐc[R] B) (hπ : Function.Surjective π) (g : A →ₐc[R] C)
    (h : ∀ a, π a = 0 → g a = 0) : (descend π hπ g h).comp π = g :=
  BialgHom.ext (descend_apply π hπ g h)

theorem toAlgHom_descend (π : A →ₐc[R] B) (hπ : Function.Surjective π) (g : A →ₐc[R] C)
    (h : ∀ a, π a = 0 → g a = 0) :
    (descend π hπ g h : B →ₐ[R] C) = descendAlgHom (π : A →ₐ[R] B) hπ (g : A →ₐ[R] C) h := rfl

theorem ker_eq_map_of_comp_eq {f : B →ₐ[R] C} {π : A →ₐ[R] B} (hπ : Function.Surjective π)
    {g : A →ₐ[R] C} (h : f.comp π = g) :
    RingHom.ker f = Ideal.map π (RingHom.ker g) := by
  have hk : RingHom.ker g = Ideal.comap π (RingHom.ker f) := by
    ext a; rw [Ideal.mem_comap, RingHom.mem_ker, RingHom.mem_ker, ← AlgHom.comp_apply, h]
  rw [hk, Ideal.map_comap_of_surjective _ hπ]

theorem map_augIdeal_le (φ : A →ₐc[R] B) :
    Ideal.map (φ : A →ₐ[R] B) (PDivisibleGroup.Hopf.augIdeal R A) ≤ PDivisibleGroup.Hopf.augIdeal R B := by
  rw [Ideal.map_le_iff_le_comap]
  intro a ha
  rw [Ideal.mem_comap, PDivisibleGroup.Hopf.mem_augIdeal_iff, BialgHom.coe_toAlgHom,
    CoalgHomClass.counit_comp_apply]
  exact ha

theorem map_augIdeal_eq (φ : A →ₐc[R] B) (hφ : Function.Surjective φ) :
    Ideal.map (φ : A →ₐ[R] B) (PDivisibleGroup.Hopf.augIdeal R A) = PDivisibleGroup.Hopf.augIdeal R B := by
  refine le_antisymm (map_augIdeal_le φ) fun b hb => ?_
  obtain ⟨a, rfl⟩ := hφ b
  have ha : a - algebraMap R A (counit (R := R) a) ∈ PDivisibleGroup.Hopf.augIdeal R A :=
    PDivisibleGroup.Hopf.sub_algebraMap_counit_mem_augIdeal R A a
  have hb' : counit (R := R) a = 0 := by
    rw [PDivisibleGroup.Hopf.mem_augIdeal_iff, CoalgHomClass.counit_comp_apply] at hb
    exact hb
  have := Ideal.mem_map_of_mem (φ : A →ₐ[R] B) ha
  rwa [hb', map_zero, sub_zero] at this

theorem exists_mem_augIdeal_apply_eq (φ : A →ₐc[R] B) (hφ : Function.Surjective φ) {b : B}
    (hb : b ∈ PDivisibleGroup.Hopf.augIdeal R B) : ∃ a ∈ PDivisibleGroup.Hopf.augIdeal R A, φ a = b := by
  obtain ⟨a, rfl⟩ := hφ b
  refine ⟨a - algebraMap R A (counit (R := R) a),
    PDivisibleGroup.Hopf.sub_algebraMap_counit_mem_augIdeal R A a, ?_⟩
  have hb' : counit (R := R) a = 0 := by
    rw [PDivisibleGroup.Hopf.mem_augIdeal_iff, CoalgHomClass.counit_comp_apply] at hb
    exact hb
  rw [hb', map_zero, sub_zero]

theorem map_torsionIdeal_eq (φ : A →ₐc[R] B) (hφ : Function.Surjective φ) (n : ℕ) :
    Ideal.map (φ : A →ₐ[R] B) (PDivisibleGroup.Hopf.torsionIdeal R A n) =
      PDivisibleGroup.Hopf.torsionIdeal R B n := by
  apply le_antisymm
  · rw [PDivisibleGroup.Hopf.torsionIdeal, Ideal.map_le_iff_le_comap, Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, Ideal.mem_comap, BialgHom.coe_toAlgHom,
      ← PDivisibleGroup.Hopf.nsmulAlgHom_bialgHom_apply φ n a]
    refine PDivisibleGroup.Hopf.nsmulAlgHom_mem_torsionIdeal R B ?_ n
    rw [PDivisibleGroup.Hopf.mem_augIdeal_iff, CoalgHomClass.counit_comp_apply]
    exact ha
  · rw [PDivisibleGroup.Hopf.torsionIdeal, Ideal.map_le_iff_le_comap]
    intro b hb
    obtain ⟨a, ha, rfl⟩ := exists_mem_augIdeal_apply_eq φ hφ hb
    rw [Ideal.mem_comap, PDivisibleGroup.Hopf.nsmulAlgHom_bialgHom_apply φ n a]
    exact Ideal.mem_map_of_mem (φ : A →ₐ[R] B) (PDivisibleGroup.Hopf.nsmulAlgHom_mem_torsionIdeal R A ha n)

theorem nsmulAlgHom_comp_nsmulAlgHom (m n : ℕ) :
    (PDivisibleGroup.Hopf.nsmulAlgHom R A m).comp (PDivisibleGroup.Hopf.nsmulAlgHom R A n) =
      PDivisibleGroup.Hopf.nsmulAlgHom R A (m * n) := by
  rw [PDivisibleGroup.Hopf.nsmulAlgHom_mul]
  apply WithConv.toConv_injective
  rw [WithConv.toConv_ofConv]
  exact (PDivisibleGroup.Hopf.toConv_pow_eq_toConv_comp_nsmulAlgHom (PDivisibleGroup.Hopf.nsmulAlgHom R A m) n).symm

theorem torsionIdeal_le_torsionIdeal_of_dvd {m n : ℕ} (h : m ∣ n) :
    PDivisibleGroup.Hopf.torsionIdeal R A n ≤ PDivisibleGroup.Hopf.torsionIdeal R A m := by
  obtain ⟨k, rfl⟩ := h
  rw [PDivisibleGroup.Hopf.torsionIdeal, PDivisibleGroup.Hopf.torsionIdeal, Ideal.map_le_iff_le_comap]
  intro a ha
  rw [Ideal.mem_comap, ← nsmulAlgHom_comp_nsmulAlgHom, AlgHom.comp_apply]
  exact PDivisibleGroup.Hopf.nsmulAlgHom_mem_torsionIdeal R A
    (PDivisibleGroup.Hopf.nsmulAlgHom_mem_augIdeal R A ha k) m

end Descend

section Datum

variable (p : ℕ) [Fact p.Prime]

structure SplitDatum (B : Type v) [CommRing B] [HopfAlgebra (ZMod p) B] where
  Bc : Type v
  [instCommRingBc : CommRing Bc]
  [instHopfBc : HopfAlgebra (ZMod p) Bc]
  [instCocommBc : Coalgebra.IsCocomm (ZMod p) Bc]
  [instFiniteBc : Module.Finite (ZMod p) Bc]
  Be : Type v
  [instCommRingBe : CommRing Be]
  [instHopfBe : HopfAlgebra (ZMod p) Be]
  [instCocommBe : Coalgebra.IsCocomm (ZMod p) Be]
  [instFiniteBe : Module.Finite (ZMod p) Be]
  qc : B →ₐc[ZMod p] Bc
  πe : B →ₐc[ZMod p] Be
  σ : Be →ₐc[ZMod p] B
  Θ : B →ₐc[ZMod p] Bc ⊗[ZMod p] Be
  isLocalRing : IsLocalRing Bc
  isReduced : IsReduced Be
  formallyUnramified : Algebra.FormallyUnramified (ZMod p) Be
  qc_surjective : Function.Surjective qc
  πe_surjective : Function.Surjective πe
  ker_πe : RingHom.ker (πe : B →ₐ[ZMod p] Be) = nilradical B
  πe_comp_σ : πe.comp σ = BialgHom.id (ZMod p) Be
  σ_unique : ∀ τ : Be →ₐ[ZMod p] B, (πe : B →ₐ[ZMod p] Be).comp τ = AlgHom.id (ZMod p) Be →
    τ = (σ : Be →ₐ[ZMod p] B)
  ker_qc : RingHom.ker (qc : B →ₐ[ZMod p] Bc) =
    Ideal.map (σ : Be →ₐ[ZMod p] B) (RingHom.ker (Bialgebra.counitAlgHom (ZMod p) Be))
  Θ_bijective : Function.Bijective Θ
  Θ_apply : ∀ b : B, Θ b = Algebra.TensorProduct.map (qc : B →ₐ[ZMod p] Bc) (πe : B →ₐ[ZMod p] Be)
    (Coalgebra.comul (R := ZMod p) b)

attribute [scoped instance] SplitDatum.instCommRingBc SplitDatum.instHopfBc SplitDatum.instCocommBc
  SplitDatum.instFiniteBc SplitDatum.instCommRingBe SplitDatum.instHopfBe SplitDatum.instCocommBe
  SplitDatum.instFiniteBe

theorem SplitDatum.nonempty (B : Type v) [CommRing B] [HopfAlgebra (ZMod p) B]
    [Coalgebra.IsCocomm (ZMod p) B] [Module.Finite (ZMod p) B] : Nonempty (SplitDatum p B) := by
  obtain ⟨Bc, _, _, _, _, Be, _, _, _, _, qc, πe, σ, Θ, hloc, hred, hfu, hqs, hπs, hker, hsec, huniq,
    hkq, hΘb, hΘ⟩ :=
    HopfAlgebra.exists_isLocalRing_isReduced_bijective_tensorProduct_comul_zmodp p B
  exact ⟨SplitDatum.mk Bc Be qc πe σ Θ hloc hred hfu hqs hπs hker hsec huniq hkq hΘb hΘ⟩

variable {p}
variable {B : Type v} [CommRing B] [HopfAlgebra (ZMod p) B] (D : SplitDatum p B)

namespace SplitDatum

theorem πe_σ (y : D.Be) : D.πe (D.σ y) = y := by
  have := DFunLike.congr_fun D.πe_comp_σ y
  rwa [BialgHom.comp_apply] at this

theorem σ_πe_sub_mem_nilradical (b : B) : D.σ (D.πe b) - b ∈ nilradical B := by
  rw [← D.ker_πe, RingHom.mem_ker, BialgHom.coe_toAlgHom, map_sub, πe_σ, sub_self]

theorem σ_mem_ker_qc {y : D.Be} (hy : counit (R := ZMod p) y = 0) : D.σ y ∈ RingHom.ker (D.qc : B →ₐ[ZMod p] D.Bc) := by
  rw [D.ker_qc]
  exact Ideal.mem_map_of_mem (D.σ : D.Be →ₐ[ZMod p] B) (by rwa [RingHom.mem_ker])

theorem qc_σ {y : D.Be} (hy : counit (R := ZMod p) y = 0) : D.qc (D.σ y) = 0 := by
  have := D.σ_mem_ker_qc hy
  rwa [RingHom.mem_ker] at this

theorem isNilpotent_ker_πe [Module.Finite (ZMod p) B] :
    IsNilpotent (RingHom.ker ((D.πe : B →ₐ[ZMod p] D.Be) : B →+* D.Be)) := by
  have h : RingHom.ker ((D.πe : B →ₐ[ZMod p] D.Be) : B →+* D.Be) = nilradical B := by
    rw [← D.ker_πe]; rfl
  rw [h]
  haveI : IsArtinianRing B := isArtinian_of_tower (ZMod p) inferInstance
  exact IsArtinianRing.isNilpotent_nilradical

end SplitDatum

end Datum

section Transition

variable {p : ℕ} [Fact p.Prime]
  {B' : Type v} [CommRing B'] [HopfAlgebra (ZMod p) B'] [Module.Finite (ZMod p) B']
  {B : Type v} [CommRing B] [HopfAlgebra (ZMod p) B] [Module.Finite (ZMod p) B]
  (D' : SplitDatum p B') (D : SplitDatum p B) (s : B' →ₐc[ZMod p] B)

namespace SplitDatum

def se : D'.Be →ₐc[ZMod p] D.Be := (D.πe.comp s).comp D'.σ

theorem se_apply (y : D'.Be) : se D' D s y = D.πe (s (D'.σ y)) := rfl

theorem se_πe (b : B') : se D' D s (D'.πe b) = D.πe (s b) := by
  rw [se_apply, ← sub_eq_zero, ← map_sub, ← map_sub, ← RingHom.mem_ker]
  change s (D'.σ (D'.πe b) - b) ∈ RingHom.ker (D.πe : B →ₐ[ZMod p] D.Be)
  rw [D.ker_πe]
  obtain ⟨n, hn⟩ := (mem_nilradical).1 (D'.σ_πe_sub_mem_nilradical b)
  exact mem_nilradical.2 ⟨n, by rw [← map_pow, hn, map_zero]⟩

theorem se_comp_πe : (se D' D s).comp D'.πe = D.πe.comp s :=
  BialgHom.ext (se_πe D' D s)

theorem se_surjective (hs : Function.Surjective s) : Function.Surjective (se D' D s) := by
  intro z
  obtain ⟨b, rfl⟩ := D.πe_surjective z
  obtain ⟨b', rfl⟩ := hs b
  exact ⟨D'.πe b', se_πe D' D s b'⟩

theorem s_comp_σ : (s : B' →ₐ[ZMod p] B).comp (D'.σ : D'.Be →ₐ[ZMod p] B') =
    (D.σ : D.Be →ₐ[ZMod p] B).comp (se D' D s : D'.Be →ₐ[ZMod p] D.Be) := by
  haveI := D'.formallyUnramified
  refine Algebra.FormallyUnramified.lift_unique' (D.πe : B →ₐ[ZMod p] D.Be) D.isNilpotent_ker_πe _ _ ?_
  refine AlgHom.ext fun y => ?_
  change D.πe (s (D'.σ y)) = D.πe (D.σ (se D' D s y))
  rw [D.πe_σ, se_apply]

theorem s_σ (y : D'.Be) : s (D'.σ y) = D.σ (se D' D s y) :=
  AlgHom.congr_fun (s_comp_σ D' D s) y

theorem s_comp_σ' : s.comp D'.σ = D.σ.comp (se D' D s) :=
  BialgHom.ext (s_σ D' D s)

theorem qc_s_eq_zero_of_qc_eq_zero {b : B'} (hb : D'.qc b = 0) : D.qc (s b) = 0 := by
  have hb' : b ∈ Ideal.map (D'.σ : D'.Be →ₐ[ZMod p] B') (RingHom.ker (Bialgebra.counitAlgHom (ZMod p) D'.Be)) := by
    rw [← D'.ker_qc, RingHom.mem_ker]; exact hb
  have hle : Ideal.map (D'.σ : D'.Be →ₐ[ZMod p] B') (RingHom.ker (Bialgebra.counitAlgHom (ZMod p) D'.Be)) ≤
      Ideal.comap (s : B' →ₐ[ZMod p] B) (RingHom.ker (D.qc : B →ₐ[ZMod p] D.Bc)) := by
    rw [Ideal.map_le_iff_le_comap]
    intro y hy
    rw [Ideal.mem_comap, Ideal.mem_comap, RingHom.mem_ker, BialgHom.coe_toAlgHom, BialgHom.coe_toAlgHom,
      BialgHom.coe_toAlgHom, s_σ]
    refine D.qc_σ ?_
    rw [RingHom.mem_ker, Bialgebra.counitAlgHom_apply] at hy
    rw [se_apply, CoalgHomClass.counit_comp_apply, CoalgHomClass.counit_comp_apply,
      CoalgHomClass.counit_comp_apply, hy]
  have := hle hb'
  rwa [Ideal.mem_comap, RingHom.mem_ker] at this

def sc : D'.Bc →ₐc[ZMod p] D.Bc :=
  descend D'.qc D'.qc_surjective (D.qc.comp s) (fun _ hb => qc_s_eq_zero_of_qc_eq_zero D' D s hb)

theorem sc_qc (b : B') : sc D' D s (D'.qc b) = D.qc (s b) :=
  descend_apply _ _ _ _ b

theorem sc_comp_qc : (sc D' D s).comp D'.qc = D.qc.comp s :=
  BialgHom.ext (sc_qc D' D s)

theorem sc_surjective (hs : Function.Surjective s) : Function.Surjective (sc D' D s) := by
  intro z
  obtain ⟨b, rfl⟩ := D.qc_surjective z
  obtain ⟨b', rfl⟩ := hs b
  exact ⟨D'.qc b', sc_qc D' D s b'⟩

theorem Θ_comp_s [Coalgebra.IsCocomm (ZMod p) B'] :
    D.Θ.comp s = (Bialgebra.TensorProduct.map (sc D' D s) (se D' D s)).comp D'.Θ := by
  refine BialgHom.ext fun b => ?_
  rw [BialgHom.comp_apply, BialgHom.comp_apply, D.Θ_apply, D'.Θ_apply, ← CoalgHomClass.map_comp_comul_apply]
  change Algebra.TensorProduct.map (D.qc : B →ₐ[ZMod p] D.Bc) (D.πe : B →ₐ[ZMod p] D.Be)
      (Algebra.TensorProduct.map (s : B' →ₐ[ZMod p] B) (s : B' →ₐ[ZMod p] B) (comul b)) =
    Algebra.TensorProduct.map (sc D' D s : D'.Bc →ₐ[ZMod p] D.Bc) (se D' D s : D'.Be →ₐ[ZMod p] D.Be)
      (Algebra.TensorProduct.map (D'.qc : B' →ₐ[ZMod p] D'.Bc) (D'.πe : B' →ₐ[ZMod p] D'.Be) (comul b))
  rw [← AlgHom.comp_apply, ← Algebra.TensorProduct.map_comp, ← AlgHom.comp_apply,
    ← Algebra.TensorProduct.map_comp]
  congr 2
  · exact congrArg BialgHom.toAlgHom (sc_comp_qc D' D s).symm
  · exact congrArg BialgHom.toAlgHom (se_comp_πe D' D s).symm

end SplitDatum

end Transition

section Perfect

variable (p : ℕ) [Fact p.Prime]

def frobLin (E : Type*) [CommRing E] [Algebra (ZMod p) E] [CharP E p] : E →ₗ[ZMod p] E where
  toFun x := x ^ p
  map_add' x y := add_pow_char x y p
  map_smul' c x := by
    simp only [RingHom.id_apply, Algebra.smul_def, mul_pow, ← map_pow, ZMod.pow_card]

theorem frobLin_apply (E : Type*) [CommRing E] [Algebra (ZMod p) E] [CharP E p] (x : E) :
    frobLin p E x = x ^ p := rfl

theorem charP_of_nontrivial (E : Type*) [CommRing E] [Algebra (ZMod p) E] [Nontrivial E] : CharP E p :=
  charP_of_injective_algebraMap (algebraMap (ZMod p) E).injective p

theorem isReduced_of_pow_injective (E : Type*) [CommRing E] (hp1 : 1 < p)
    (h : Function.Injective fun x : E => x ^ p) : IsReduced E := by
  refine ⟨fun x hx => ?_⟩
  obtain ⟨m, hm⟩ := hx

  have hk : x ^ p ^ m = 0 := by
    have hle : m ≤ p ^ m := (Nat.lt_pow_self hp1).le
    obtain ⟨r, hr⟩ := Nat.exists_eq_add_of_le hle
    rw [hr, pow_add, hm, zero_mul]
  have key : ∀ k : ℕ, x ^ p ^ k = 0 → x = 0 := by
    intro k
    induction k with
    | zero => intro h0; simpa using h0
    | succ k ih =>
      intro hk'
      apply ih
      apply h
      dsimp only
      rw [← pow_mul, ← pow_succ, hk', zero_pow (by omega)]
  exact key m hk

theorem isReduced_quotient (E : Type*) [CommRing E] [Algebra (ZMod p) E] [Module.Finite (ZMod p) E]
    [IsReduced E] (I : Ideal E) : IsReduced (E ⧸ I) := by
  classical
  by_cases hI : I = ⊤
  · haveI : Subsingleton (E ⧸ I) := Ideal.Quotient.subsingleton_iff.2 hI
    infer_instance
  haveI : Nontrivial (E ⧸ I) := Ideal.Quotient.nontrivial_iff.2 hI
  haveI : Nontrivial E := (Ideal.Quotient.mk I).domain_nontrivial
  haveI : CharP E p := charP_of_nontrivial p E
  haveI : CharP (E ⧸ I) p := charP_of_nontrivial p (E ⧸ I)
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt

  have hinj : Function.Injective (frobLin p E) := by
    intro x y hxy
    rw [frobLin_apply, frobLin_apply] at hxy
    exact frobenius_inj E p hxy
  have hsurj : Function.Surjective (frobLin p E) := LinearMap.surjective_of_injective hinj

  have hsurj' : Function.Surjective (frobLin p (E ⧸ I)) := by
    intro z
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨y, hy⟩ := hsurj x
    refine ⟨Ideal.Quotient.mk I y, ?_⟩
    rw [frobLin_apply] at hy ⊢
    rw [← map_pow, hy]

  have hinj' : Function.Injective (frobLin p (E ⧸ I)) :=
    LinearMap.injective_iff_surjective.2 hsurj'
  exact isReduced_of_pow_injective p (E ⧸ I) hp1 hinj'

theorem radical_eq_of_isReduced (E : Type*) [CommRing E] [Algebra (ZMod p) E] [Module.Finite (ZMod p) E]
    [IsReduced E] (I : Ideal E) : I.radical = I := by
  haveI := isReduced_quotient p E I
  exact (I.isRadical_iff_quotient_reduced.2 inferInstance).radical

end Perfect

section Kernels

variable {p : ℕ} [Fact p.Prime]
  {B' : Type v} [CommRing B'] [HopfAlgebra (ZMod p) B'] [Module.Finite (ZMod p) B']
  {B : Type v} [CommRing B] [HopfAlgebra (ZMod p) B] [Module.Finite (ZMod p) B]
  (D' : SplitDatum p B') (D : SplitDatum p B) (s : B' →ₐc[ZMod p] B)

namespace SplitDatum

theorem ker_toAlgHom {R A C : Type*} [CommSemiring R] [Semiring A] [Semiring C] [Bialgebra R A]
    [Bialgebra R C] (f : A →ₐc[R] C) : RingHom.ker (f : A →ₐ[R] C) = RingHom.ker f := rfl

theorem map_s_ker_qc (hs : Function.Surjective s) :
    Ideal.map (s : B' →ₐ[ZMod p] B) (RingHom.ker (D'.qc : B' →ₐ[ZMod p] D'.Bc)) =
      RingHom.ker (D.qc : B →ₐ[ZMod p] D.Bc) := by
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro b hb
    rw [Ideal.mem_comap, RingHom.mem_ker, BialgHom.coe_toAlgHom, BialgHom.coe_toAlgHom]
    exact qc_s_eq_zero_of_qc_eq_zero D' D s (by rwa [RingHom.mem_ker] at hb)
  · rw [D.ker_qc, Ideal.map_le_iff_le_comap]
    intro z hz
    obtain ⟨y, hy, rfl⟩ := exists_mem_augIdeal_apply_eq (se D' D s) (se_surjective D' D s hs)
      (b := z) hz
    rw [Ideal.mem_comap, BialgHom.coe_toAlgHom, ← s_σ]
    exact Ideal.mem_map_of_mem (s : B' →ₐ[ZMod p] B) (D'.σ_mem_ker_qc hy)

theorem ker_sc (hs : Function.Surjective s) (n : ℕ)
    (hkers : RingHom.ker s = PDivisibleGroup.Hopf.torsionIdeal (ZMod p) B' n) :
    RingHom.ker (sc D' D s) = PDivisibleGroup.Hopf.torsionIdeal (ZMod p) D'.Bc n := by
  have h1 : RingHom.ker (sc D' D s : D'.Bc →ₐ[ZMod p] D.Bc) =
      Ideal.map (D'.qc : B' →ₐ[ZMod p] D'.Bc) (RingHom.ker ((D.qc : B →ₐ[ZMod p] D.Bc).comp (s : B' →ₐ[ZMod p] B))) :=
    ker_eq_map_of_comp_eq D'.qc_surjective (congrArg BialgHom.toAlgHom (sc_comp_qc D' D s))
  have h2 : RingHom.ker ((D.qc : B →ₐ[ZMod p] D.Bc).comp (s : B' →ₐ[ZMod p] B)) =
      RingHom.ker (D'.qc : B' →ₐ[ZMod p] D'.Bc) ⊔ RingHom.ker (s : B' →ₐ[ZMod p] B) := by
    rw [RingHom.ker_eq_comap_bot, ← Ideal.comap_comapₐ, ← RingHom.ker_eq_comap_bot, ← map_s_ker_qc D' D s hs]
    change Ideal.comap (s : B' →ₐ[ZMod p] B) (Ideal.map (s : B' →ₐ[ZMod p] B) _) = _
    rw [Ideal.comap_map_of_surjective (s : B' →ₐ[ZMod p] B) hs, ← RingHom.ker_eq_comap_bot]
  have h3 : Ideal.map (D'.qc : B' →ₐ[ZMod p] D'.Bc) (RingHom.ker (D'.qc : B' →ₐ[ZMod p] D'.Bc)) = ⊥ := by
    rw [← le_bot_iff, Ideal.map_le_iff_le_comap, ← RingHom.ker_eq_comap_bot]
  rw [← ker_toAlgHom, h1, h2, Ideal.map_sup, h3, bot_sup_eq, ker_toAlgHom, hkers]
  exact map_torsionIdeal_eq D'.qc D'.qc_surjective n

theorem ker_se (n : ℕ)
    (hkers : RingHom.ker s = PDivisibleGroup.Hopf.torsionIdeal (ZMod p) B' n) :
    RingHom.ker (se D' D s) = PDivisibleGroup.Hopf.torsionIdeal (ZMod p) D'.Be n := by
  haveI := D'.isReduced
  have h1 : RingHom.ker (se D' D s : D'.Be →ₐ[ZMod p] D.Be) =
      Ideal.map (D'.πe : B' →ₐ[ZMod p] D'.Be) (RingHom.ker ((D.πe : B →ₐ[ZMod p] D.Be).comp (s : B' →ₐ[ZMod p] B))) :=
    ker_eq_map_of_comp_eq D'.πe_surjective (congrArg BialgHom.toAlgHom (se_comp_πe D' D s))
  have h2 : RingHom.ker ((D.πe : B →ₐ[ZMod p] D.Be).comp (s : B' →ₐ[ZMod p] B)) =
      (RingHom.ker (s : B' →ₐ[ZMod p] B)).radical := by
    rw [RingHom.ker_eq_comap_bot, ← Ideal.comap_comapₐ, ← RingHom.ker_eq_comap_bot, D.ker_πe,
      nilradical, Ideal.comap_radical, Ideal.zero_eq_bot, ← RingHom.ker_eq_comap_bot]
  rw [← ker_toAlgHom, h1, h2, ker_toAlgHom, hkers]
  apply le_antisymm
  · refine (Ideal.map_radical_le _).trans ?_
    rw [map_torsionIdeal_eq D'.πe D'.πe_surjective n, radical_eq_of_isReduced p D'.Be]
  · rw [← map_torsionIdeal_eq D'.πe D'.πe_surjective n]
    exact Ideal.map_mono (Ideal.le_radical)

end SplitDatum

end Kernels

section NSMulBialg

variable (R : Type*) [CommRing R] (A : Type*) [CommRing A] [Bialgebra R A] [Coalgebra.IsCocomm R A]

def nsmulBialgHom (n : ℕ) : A →ₐc[R] A := ((WithConv.toConv (BialgHom.id R A)) ^ n).ofConv

theorem toAlgHom_nsmulBialgHom (n : ℕ) :
    (nsmulBialgHom R A n : A →ₐ[R] A) = PDivisibleGroup.Hopf.nsmulAlgHom R A n := by
  have h := BialgHom.toAlgHom_convPow (WithConv.toConv (BialgHom.id R A)) n
  apply WithConv.toConv_injective
  exact h

end NSMulBialg

section Ranks

variable {p : ℕ} [Fact p.Prime]

abbrev tors (C : Type*) [CommRing C] [Bialgebra (ZMod p) C] (n : ℕ) : Ideal C :=
  PDivisibleGroup.Hopf.torsionIdeal (ZMod p) C n

def Killed (C : Type*) [CommRing C] [Bialgebra (ZMod p) C] (N : ℕ) : Prop :=
  PDivisibleGroup.Hopf.nsmulAlgHom (ZMod p) C N =
    (Algebra.ofId (ZMod p) C).comp (Bialgebra.counitAlgHom (ZMod p) C)

variable (p)

theorem killed_iff (C : Type*) [CommRing C] [Bialgebra (ZMod p) C] (N : ℕ) :
    Killed (p := p) C N ↔ ∀ c ∈ PDivisibleGroup.Hopf.augIdeal (ZMod p) C,
      PDivisibleGroup.Hopf.nsmulAlgHom (ZMod p) C N c = 0 := by
  constructor
  · intro h c hc
    rw [Killed] at h
    rw [h, AlgHom.comp_apply, Bialgebra.counitAlgHom_apply, (PDivisibleGroup.Hopf.mem_augIdeal_iff _ _ c).1 hc,
      map_zero]
  · intro h
    refine AlgHom.ext fun c => ?_
    have hc := PDivisibleGroup.Hopf.sub_algebraMap_counit_mem_augIdeal (ZMod p) C c
    have h1 := h _ hc
    rw [map_sub, PDivisibleGroup.Hopf.nsmulAlgHom_algebraMap, sub_eq_zero] at h1
    rw [h1]
    rfl

variable {p}

theorem killed_of_surjective {A C : Type*} [CommRing A] [Bialgebra (ZMod p) A] [CommRing C] [Bialgebra (ZMod p) C]
    (φ : A →ₐc[ZMod p] C) (hφ : Function.Surjective φ) {N : ℕ} (h : Killed (p := p) A N) :
    Killed (p := p) C N := by
  rw [killed_iff] at h ⊢
  intro c hc
  obtain ⟨a, ha, rfl⟩ := exists_mem_augIdeal_apply_eq φ hφ hc
  rw [PDivisibleGroup.Hopf.nsmulAlgHom_bialgHom_apply, h a ha, map_zero]

theorem tors_eq_bot_of_killed {C : Type*} [CommRing C] [Bialgebra (ZMod p) C] {N : ℕ}
    (h : Killed (p := p) C N) : tors (p := p) C N = ⊥ := by
  rw [← le_bot_iff, tors, PDivisibleGroup.Hopf.torsionIdeal, Ideal.map_le_iff_le_comap]
  intro c hc
  rw [Ideal.mem_comap, (killed_iff p C N).1 h c hc]
  exact Ideal.zero_mem _

theorem tors_le_ker_nsmulAlgHom {C : Type*} [CommRing C] [Bialgebra (ZMod p) C] {N m : ℕ}
    (h : Killed (p := p) C (m * N)) :
    tors (p := p) C N ≤ RingHom.ker (PDivisibleGroup.Hopf.nsmulAlgHom (ZMod p) C m) := by
  rw [tors, PDivisibleGroup.Hopf.torsionIdeal, Ideal.map_le_iff_le_comap]
  intro c hc
  rw [Ideal.mem_comap, RingHom.mem_ker, ← AlgHom.comp_apply, nsmulAlgHom_comp_nsmulAlgHom]
  exact (killed_iff p C _).1 h c hc

theorem finrank_eq_finrank_quot_tors_mul (C : Type v) [CommRing C] [HopfAlgebra (ZMod p) C]
    [Coalgebra.IsCocomm (ZMod p) C] [Module.Finite (ZMod p) C] (n : ℕ) :
    Module.finrank (ZMod p) C = Module.finrank (ZMod p) (C ⧸ tors (p := p) C n) *
      Module.finrank (ZMod p) (LinearMap.range (PDivisibleGroup.Hopf.nsmulAlgHom (ZMod p) C n).toLinearMap) := by
  have h := HopfAlgebra.finrank_eq_finrank_quotient_map_ker_counit_mul_finrank_range (ZMod p)
    (nsmulBialgHom (ZMod p) C n)
  rw [toAlgHom_nsmulBialgHom] at h
  rw [h]

  congr 1

theorem finrank_range_nsmulAlgHom_le {C : Type v} [CommRing C] [HopfAlgebra (ZMod p) C]
    [Module.Finite (ZMod p) C] {N m : ℕ} (h : Killed (p := p) C (m * N)) :
    Module.finrank (ZMod p) (LinearMap.range (PDivisibleGroup.Hopf.nsmulAlgHom (ZMod p) C m).toLinearMap) ≤
      Module.finrank (ZMod p) (C ⧸ tors (p := p) C N) := by
  set f := PDivisibleGroup.Hopf.nsmulAlgHom (ZMod p) C m
  have hle := tors_le_ker_nsmulAlgHom (p := p) h
  let g : (C ⧸ tors (p := p) C N) →ₐ[ZMod p] C :=
    Ideal.Quotient.liftₐ (tors (p := p) C N) f (fun c hc => (RingHom.mem_ker).1 (hle hc))
  have hfg : f.toLinearMap = g.toLinearMap ∘ₗ (Ideal.Quotient.mkₐ (ZMod p) (tors (p := p) C N)).toLinearMap := by
    refine LinearMap.ext fun c => ?_
    rfl
  have hrange : LinearMap.range f.toLinearMap = LinearMap.range g.toLinearMap := by
    rw [hfg]
    exact LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.2 Ideal.Quotient.mk_surjective)
  rw [hrange]
  exact LinearMap.finrank_range_le g.toLinearMap

theorem finrank_quot_eq_of_surjective {C : Type v} {C₀ : Type w} [CommRing C] [CommRing C₀]
    [Algebra (ZMod p) C] [Algebra (ZMod p) C₀] (f : C →ₐ[ZMod p] C₀) (hf : Function.Surjective f)
    {I : Ideal C} (hI : RingHom.ker f = I) :
    Module.finrank (ZMod p) (C ⧸ I) = Module.finrank (ZMod p) C₀ := by
  subst hI
  exact (Ideal.quotientKerAlgEquivOfSurjective hf).toLinearEquiv.finrank_eq

theorem finrank_eq_mul_of_bijective {C : Type v} [CommRing C] [HopfAlgebra (ZMod p) C] (D : SplitDatum p C)
    [Module.Finite (ZMod p) C] :
    Module.finrank (ZMod p) C = Module.finrank (ZMod p) D.Bc * Module.finrank (ZMod p) D.Be := by
  rw [(LinearEquiv.ofBijective (D.Θ : C →ₐc[ZMod p] D.Bc ⊗[ZMod p] D.Be).toLinearMap D.Θ_bijective).finrank_eq,
    Module.finrank_tensorProduct]

theorem finrank_quot_tors_eq_of_surjective {C' C : Type v} [CommRing C'] [CommRing C]
    [HopfAlgebra (ZMod p) C'] [HopfAlgebra (ZMod p) C] (φ : C' →ₐc[ZMod p] C)
    (hφ : Function.Surjective φ) {N : ℕ} (hker : RingHom.ker (φ : C' →ₐ[ZMod p] C) ≤ tors (p := p) C' N) :
    Module.finrank (ZMod p) (C' ⧸ tors (p := p) C' N) = Module.finrank (ZMod p) (C ⧸ tors (p := p) C N) := by
  let g : C' →ₐ[ZMod p] C ⧸ tors (p := p) C N := (Ideal.Quotient.mkₐ (ZMod p) _).comp (φ : C' →ₐ[ZMod p] C)
  have hg : Function.Surjective g := Ideal.Quotient.mk_surjective.comp hφ
  have hk : RingHom.ker g = tors (p := p) C' N := by
    ext c
    rw [RingHom.mem_ker, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
    change (φ : C' →ₐ[ZMod p] C) c ∈ PDivisibleGroup.Hopf.torsionIdeal (ZMod p) C N ↔
      c ∈ PDivisibleGroup.Hopf.torsionIdeal (ZMod p) C' N
    rw [← map_torsionIdeal_eq φ hφ N, ← Ideal.mem_comap]
    change c ∈ Ideal.comap (φ : C' →ₐ[ZMod p] C) (Ideal.map (φ : C' →ₐ[ZMod p] C) (tors (p := p) C' N)) ↔ _
    rw [Ideal.comap_map_of_surjective (φ : C' →ₐ[ZMod p] C) hφ, ← RingHom.ker_eq_comap_bot, sup_eq_left.2 hker]
  exact finrank_quot_eq_of_surjective g hg hk

theorem eq_of_le_of_le_of_mul_eq {c d x y : ℕ} (hc : c ≤ x) (hd : d ≤ y) (h : c * d = x * y) (hxy : x * y ≠ 0) :
    c = x := by
  by_contra hne
  have hlt : c < x := lt_of_le_of_ne hc hne
  have hy : 0 < y := Nat.pos_of_ne_zero fun hy => hxy (by rw [hy, mul_zero])
  have : c * d < x * y := calc
    c * d ≤ c * y := Nat.mul_le_mul_left c hd
    _ < x * y := Nat.mul_lt_mul_of_lt_of_le hlt le_rfl hy
  exact absurd h this.ne

end Ranks

section Tower

variable {p : ℕ} [Fact p.Prime] (h : ℕ)
  (G : ℕ → Type v) [∀ v, CommRing (G v)] [∀ v, HopfAlgebra (ZMod p) (G v)]
  [∀ v, Coalgebra.IsCocomm (ZMod p) (G v)] [∀ v, Module.Finite (ZMod p) (G v)]
  (s : ∀ v, G (v + 1) →ₐc[ZMod p] G v) (hs : ∀ v, Function.Surjective (s v))
  (hrankG : ∀ v, Module.finrank (ZMod p) (G v) = p ^ (v * h))
  (hkerG : ∀ v, RingHom.ker (s v) = PDivisibleGroup.Hopf.torsionIdeal (ZMod p) (G (v + 1)) (p ^ v))
  (D : ∀ v, SplitDatum p (G v))

include hs hrankG hkerG

theorem killed_level (v : ℕ) : Killed (p := p) (G (v + 1)) (p ^ (v + 1)) := by
  rw [killed_iff]
  intro b hb
  obtain ⟨a, ha, rfl⟩ := exists_mem_augIdeal_apply_eq (s (v + 1)) (hs (v + 1)) hb
  rw [PDivisibleGroup.Hopf.nsmulAlgHom_bialgHom_apply]
  have hmem : PDivisibleGroup.Hopf.nsmulAlgHom (ZMod p) (G (v + 1 + 1)) (p ^ (v + 1)) a ∈ RingHom.ker (s (v + 1)) := by
    rw [hkerG (v + 1)]
    exact PDivisibleGroup.Hopf.nsmulAlgHom_mem_torsionIdeal (ZMod p) _ ha _
  exact (RingHom.mem_ker).1 hmem

section WithDatum

theorem killed_Bc (v : ℕ) : Killed (p := p) (D (v + 1)).Bc (p ^ (v + 1)) :=
  killed_of_surjective (D (v + 1)).qc (D (v + 1)).qc_surjective (killed_level h G s hs hrankG hkerG v)

theorem killed_Be (v : ℕ) : Killed (p := p) (D (v + 1)).Be (p ^ (v + 1)) :=
  killed_of_surjective (D (v + 1)).πe (D (v + 1)).πe_surjective (killed_level h G s hs hrankG hkerG v)

theorem finrank_Bc_mul_finrank_Be (v : ℕ) :
    Module.finrank (ZMod p) (D v).Bc * Module.finrank (ZMod p) (D v).Be = p ^ (v * h) := by
  rw [← finrank_eq_mul_of_bijective (D v), hrankG]

theorem finrank_Bc_succ (v : ℕ) :
    Module.finrank (ZMod p) (D (v + 1)).Bc = Module.finrank (ZMod p) (D v).Bc *
      Module.finrank (ZMod p) (LinearMap.range
        (PDivisibleGroup.Hopf.nsmulAlgHom (ZMod p) (D (v + 1)).Bc (p ^ v)).toLinearMap) := by
  rw [finrank_eq_finrank_quot_tors_mul (p := p) (D (v + 1)).Bc (p ^ v)]
  congr 1
  refine finrank_quot_eq_of_surjective (SplitDatum.sc (D (v + 1)) (D v) (s v) : _ →ₐ[ZMod p] _)
    (SplitDatum.sc_surjective _ _ _ (hs v)) ?_
  rw [SplitDatum.ker_toAlgHom]
  exact SplitDatum.ker_sc (D (v + 1)) (D v) (s v) (hs v) (p ^ v) (hkerG v)

theorem finrank_Be_succ (v : ℕ) :
    Module.finrank (ZMod p) (D (v + 1)).Be = Module.finrank (ZMod p) (D v).Be *
      Module.finrank (ZMod p) (LinearMap.range
        (PDivisibleGroup.Hopf.nsmulAlgHom (ZMod p) (D (v + 1)).Be (p ^ v)).toLinearMap) := by
  rw [finrank_eq_finrank_quot_tors_mul (p := p) (D (v + 1)).Be (p ^ v)]
  congr 1
  refine finrank_quot_eq_of_surjective (SplitDatum.se (D (v + 1)) (D v) (s v) : _ →ₐ[ZMod p] _)
    (SplitDatum.se_surjective _ _ _ (hs v)) ?_
  rw [SplitDatum.ker_toAlgHom]
  exact SplitDatum.ker_se (D (v + 1)) (D v) (s v) (p ^ v) (hkerG v)

theorem finrank_range_Bc_le (v : ℕ) :
    Module.finrank (ZMod p) (LinearMap.range
        (PDivisibleGroup.Hopf.nsmulAlgHom (ZMod p) (D (v + 1)).Bc (p ^ v)).toLinearMap) ≤
      Module.finrank (ZMod p) ((D (v + 1)).Bc ⧸ tors (p := p) (D (v + 1)).Bc p) := by
  refine finrank_range_nsmulAlgHom_le (p := p) ?_
  rw [← pow_succ]
  exact killed_Bc h G s hs hrankG hkerG D v

theorem finrank_range_Be_le (v : ℕ) :
    Module.finrank (ZMod p) (LinearMap.range
        (PDivisibleGroup.Hopf.nsmulAlgHom (ZMod p) (D (v + 1)).Be (p ^ v)).toLinearMap) ≤
      Module.finrank (ZMod p) ((D (v + 1)).Be ⧸ tors (p := p) (D (v + 1)).Be p) := by
  refine finrank_range_nsmulAlgHom_le (p := p) ?_
  rw [← pow_succ]
  exact killed_Be h G s hs hrankG hkerG D v

theorem finrank_quot_tors_Bc (v : ℕ) :
    Module.finrank (ZMod p) ((D (v + 1)).Bc ⧸ tors (p := p) (D (v + 1)).Bc p) =
      Module.finrank (ZMod p) (D 1).Bc := by
  induction v with
  | zero =>
    have hbot : tors (p := p) (D 1).Bc p = ⊥ := by
      have hk := killed_Bc h G s hs hrankG hkerG D 0
      rw [zero_add, pow_one] at hk
      exact tors_eq_bot_of_killed hk
    refine finrank_quot_eq_of_surjective (AlgHom.id (ZMod p) (D 1).Bc) Function.surjective_id ?_
    rw [hbot]
    exact (RingHom.injective_iff_ker_eq_bot _).1 Function.injective_id
  | succ v ih =>
    rw [← ih]
    refine finrank_quot_tors_eq_of_surjective (SplitDatum.sc (D (v + 1 + 1)) (D (v + 1)) (s (v + 1)))
      (SplitDatum.sc_surjective _ _ _ (hs (v + 1))) ?_
    rw [SplitDatum.ker_toAlgHom, SplitDatum.ker_sc (D (v + 1 + 1)) (D (v + 1)) (s (v + 1)) (hs (v + 1))
      (p ^ (v + 1)) (hkerG (v + 1))]
    exact torsionIdeal_le_torsionIdeal_of_dvd (dvd_pow_self p (Nat.succ_ne_zero v))

theorem finrank_quot_tors_Be (v : ℕ) :
    Module.finrank (ZMod p) ((D (v + 1)).Be ⧸ tors (p := p) (D (v + 1)).Be p) =
      Module.finrank (ZMod p) (D 1).Be := by
  induction v with
  | zero =>
    have hbot : tors (p := p) (D 1).Be p = ⊥ := by
      have hk := killed_Be h G s hs hrankG hkerG D 0
      rw [zero_add, pow_one] at hk
      exact tors_eq_bot_of_killed hk
    refine finrank_quot_eq_of_surjective (AlgHom.id (ZMod p) (D 1).Be) Function.surjective_id ?_
    rw [hbot]
    exact (RingHom.injective_iff_ker_eq_bot _).1 Function.injective_id
  | succ v ih =>
    rw [← ih]
    refine finrank_quot_tors_eq_of_surjective (SplitDatum.se (D (v + 1 + 1)) (D (v + 1)) (s (v + 1)))
      (SplitDatum.se_surjective _ _ _ (hs (v + 1))) ?_
    rw [SplitDatum.ker_toAlgHom, SplitDatum.ker_se (D (v + 1 + 1)) (D (v + 1)) (s (v + 1))
      (p ^ (v + 1)) (hkerG (v + 1))]
    exact torsionIdeal_le_torsionIdeal_of_dvd (dvd_pow_self p (Nat.succ_ne_zero v))

theorem finrank_succ_eq (v : ℕ) :
    Module.finrank (ZMod p) (D (v + 1)).Bc = Module.finrank (ZMod p) (D v).Bc * Module.finrank (ZMod p) (D 1).Bc ∧
    Module.finrank (ZMod p) (D (v + 1)).Be = Module.finrank (ZMod p) (D v).Be * Module.finrank (ZMod p) (D 1).Be := by
  have hp : 0 < p := (Fact.out : p.Prime).pos

  set x := fun w => Module.finrank (ZMod p) (D w).Bc with hx
  set y := fun w => Module.finrank (ZMod p) (D w).Be with hy
  set c := Module.finrank (ZMod p) (LinearMap.range
        (PDivisibleGroup.Hopf.nsmulAlgHom (ZMod p) (D (v + 1)).Bc (p ^ v)).toLinearMap) with hc
  set d := Module.finrank (ZMod p) (LinearMap.range
        (PDivisibleGroup.Hopf.nsmulAlgHom (ZMod p) (D (v + 1)).Be (p ^ v)).toLinearMap) with hd
  have hxs : x (v + 1) = x v * c := finrank_Bc_succ h G s hs hrankG hkerG D v
  have hys : y (v + 1) = y v * d := finrank_Be_succ h G s hs hrankG hkerG D v
  have hcle : c ≤ x 1 := (finrank_range_Bc_le h G s hs hrankG hkerG D v).trans (finrank_quot_tors_Bc h G s hs hrankG hkerG D v).le
  have hdle : d ≤ y 1 := (finrank_range_Be_le h G s hs hrankG hkerG D v).trans (finrank_quot_tors_Be h G s hs hrankG hkerG D v).le
  have hxy : ∀ w, x w * y w = p ^ (w * h) := fun w => finrank_Bc_mul_finrank_Be h G s hs hrankG hkerG D w
  have h1 : x 1 * y 1 = p ^ h := by rw [hxy, one_mul]

  have hcd : c * d = x 1 * y 1 := by
    have e1 : x (v + 1) * y (v + 1) = (x v * y v) * (c * d) := by rw [hxs, hys]; ring
    rw [hxy, hxy, Nat.succ_mul, pow_add, ← h1] at e1
    exact (Nat.eq_of_mul_eq_mul_left (pow_pos hp _) e1).symm
  have hne : x 1 * y 1 ≠ 0 := by rw [h1]; exact (pow_pos hp _).ne'
  have hcx : c = x 1 := eq_of_le_of_le_of_mul_eq hcle hdle hcd hne
  have hdy : d = y 1 := eq_of_le_of_le_of_mul_eq hdle hcle (by rw [mul_comm, hcd, mul_comm]) (by rwa [mul_comm])
  constructor
  · have e := hxs
    rw [hcx] at e
    exact e
  · have e := hys
    rw [hdy] at e
    exact e

theorem finrank_eq_pow (v : ℕ) :
    Module.finrank (ZMod p) (D v).Bc = Module.finrank (ZMod p) (D 1).Bc ^ v ∧
    Module.finrank (ZMod p) (D v).Be = Module.finrank (ZMod p) (D 1).Be ^ v := by
  induction v with
  | zero =>
    have h0 := finrank_Bc_mul_finrank_Be h G s hs hrankG hkerG D 0
    rw [zero_mul, pow_zero] at h0
    exact ⟨by rw [pow_zero]; exact Nat.eq_one_of_mul_eq_one_right h0,
      by rw [pow_zero]; exact Nat.eq_one_of_mul_eq_one_left h0⟩
  | succ v ih =>
    obtain ⟨h1, h2⟩ := finrank_succ_eq h G s hs hrankG hkerG D v
    exact ⟨by rw [h1, ih.1, pow_succ], by rw [h2, ih.2, pow_succ]⟩

end WithDatum

include D in

theorem main :
    ∃ (hc he : ℕ)
      (Gc : ℕ → Type v) (_ : ∀ v, CommRing (Gc v)) (_ : ∀ v, HopfAlgebra (ZMod p) (Gc v))
      (_ : ∀ v, Coalgebra.IsCocomm (ZMod p) (Gc v)) (_ : ∀ v, Module.Finite (ZMod p) (Gc v))
      (Ge : ℕ → Type v) (_ : ∀ v, CommRing (Ge v)) (_ : ∀ v, HopfAlgebra (ZMod p) (Ge v))
      (_ : ∀ v, Coalgebra.IsCocomm (ZMod p) (Ge v)) (_ : ∀ v, Module.Finite (ZMod p) (Ge v))
      (sc : ∀ v, Gc (v + 1) →ₐc[ZMod p] Gc v) (se : ∀ v, Ge (v + 1) →ₐc[ZMod p] Ge v)
      (qc : ∀ v, G v →ₐc[ZMod p] Gc v) (πe : ∀ v, G v →ₐc[ZMod p] Ge v)
      (σ : ∀ v, Ge v →ₐc[ZMod p] G v)
      (Θ : ∀ v, G v →ₐc[ZMod p] Gc v ⊗[ZMod p] Ge v),
      hc + he = h ∧
      (∀ v, IsLocalRing (Gc v)) ∧ (∀ v, IsReduced (Ge v)) ∧
      (∀ v, Algebra.FormallyUnramified (ZMod p) (Ge v)) ∧
      (∀ v, Function.Surjective (sc v)) ∧
      (∀ v, Module.finrank (ZMod p) (Gc v) = p ^ (v * hc)) ∧
      (∀ v, RingHom.ker (sc v) = PDivisibleGroup.Hopf.torsionIdeal (ZMod p) (Gc (v + 1)) (p ^ v)) ∧
      (∀ v, Function.Surjective (se v)) ∧
      (∀ v, Module.finrank (ZMod p) (Ge v) = p ^ (v * he)) ∧
      (∀ v, RingHom.ker (se v) = PDivisibleGroup.Hopf.torsionIdeal (ZMod p) (Ge (v + 1)) (p ^ v)) ∧
      (∀ v, Function.Surjective (qc v)) ∧ (∀ v, Function.Surjective (πe v)) ∧
      (∀ v, RingHom.ker (πe v : G v →ₐ[ZMod p] Ge v) = nilradical (G v)) ∧
      (∀ v, (πe v).comp (σ v) = BialgHom.id (ZMod p) (Ge v)) ∧
      (∀ v, RingHom.ker (qc v : G v →ₐ[ZMod p] Gc v) =
        Ideal.map (σ v : Ge v →ₐ[ZMod p] G v)
          (RingHom.ker (Bialgebra.counitAlgHom (ZMod p) (Ge v)))) ∧
      (∀ v, Function.Bijective (Θ v)) ∧
      (∀ v b, Θ v b = Algebra.TensorProduct.map (qc v : G v →ₐ[ZMod p] Gc v)
        (πe v : G v →ₐ[ZMod p] Ge v) (Coalgebra.comul (R := ZMod p) b)) ∧
      (∀ v, (qc v).comp (s v) = (sc v).comp (qc (v + 1))) ∧
      (∀ v, (πe v).comp (s v) = (se v).comp (πe (v + 1))) ∧
      (∀ v, (s v).comp (σ (v + 1)) = (σ v).comp (se v)) ∧
      (∀ v, (Θ v).comp (s v) = (Bialgebra.TensorProduct.map (sc v) (se v)).comp (Θ (v + 1))) := by
  classical
  have hp : p.Prime := Fact.out

  have h1 : Module.finrank (ZMod p) (D 1).Bc * Module.finrank (ZMod p) (D 1).Be = p ^ h := by
    rw [finrank_Bc_mul_finrank_Be h G s hs hrankG hkerG D 1, one_mul]
  obtain ⟨hc, hhc, hxc⟩ := (Nat.dvd_prime_pow hp).1 (Dvd.intro _ h1)
  have hye : Module.finrank (ZMod p) (D 1).Be = p ^ (h - hc) := by
    have e : p ^ hc * Module.finrank (ZMod p) (D 1).Be = p ^ hc * p ^ (h - hc) := by
      rw [← pow_add, Nat.add_sub_cancel' hhc, ← h1, hxc]
    exact Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos _) e
  refine ⟨hc, h - hc, fun v => (D v).Bc, fun v => inferInstance, fun v => inferInstance, fun v => inferInstance,
    fun v => inferInstance, fun v => (D v).Be, fun v => inferInstance, fun v => inferInstance,
    fun v => inferInstance, fun v => inferInstance,
    fun v => SplitDatum.sc (D (v + 1)) (D v) (s v), fun v => SplitDatum.se (D (v + 1)) (D v) (s v),
    fun v => (D v).qc, fun v => (D v).πe, fun v => (D v).σ, fun v => (D v).Θ,
    Nat.add_sub_cancel' hhc, fun v => (D v).isLocalRing, fun v => (D v).isReduced,
    fun v => (D v).formallyUnramified,
    fun v => SplitDatum.sc_surjective _ _ _ (hs v), fun v => ?_,
    fun v => SplitDatum.ker_sc _ _ _ (hs v) _ (hkerG v),
    fun v => SplitDatum.se_surjective _ _ _ (hs v), fun v => ?_,
    fun v => SplitDatum.ker_se _ _ _ _ (hkerG v),
    fun v => (D v).qc_surjective, fun v => (D v).πe_surjective, fun v => (D v).ker_πe,
    fun v => (D v).πe_comp_σ, fun v => (D v).ker_qc, fun v => (D v).Θ_bijective, fun v => (D v).Θ_apply,
    fun v => (SplitDatum.sc_comp_qc _ _ _).symm, fun v => (SplitDatum.se_comp_πe _ _ _).symm,
    fun v => SplitDatum.s_comp_σ' _ _ _, fun v => SplitDatum.Θ_comp_s _ _ _⟩
  · rw [(finrank_eq_pow h G s hs hrankG hkerG D v).1, hxc, ← pow_mul, mul_comm]
  · rw [(finrank_eq_pow h G s hs hrankG hkerG D v).2, hye, ← pow_mul, mul_comm]

end Tower

end S42Tower
p2m_reactivate "P2MW.S_PDivisibleGroup_exists_tower_isLocalRing_isReduced_bijective_tensorProduct_comul_zmodp.S42Tower"

end
p2m_reactivate "P2MW.S_PDivisibleGroup_exists_tower_isLocalRing_isReduced_bijective_tensorProduct_comul_zmodp.S42Tower"

theorem solution
    (p : ℕ) [Fact p.Prime] (h : ℕ)
    (G : ℕ → Type v) [∀ v, CommRing (G v)] [∀ v, HopfAlgebra (ZMod p) (G v)]
    [∀ v, Coalgebra.IsCocomm (ZMod p) (G v)] [∀ v, Module.Finite (ZMod p) (G v)]
    (s : ∀ v, G (v + 1) →ₐc[ZMod p] G v) (hs : ∀ v, Function.Surjective (s v))
    (hrankG : ∀ v, Module.finrank (ZMod p) (G v) = p ^ (v * h))
    (hkerG : ∀ v, RingHom.ker (s v) = PDivisibleGroup.Hopf.torsionIdeal (ZMod p) (G (v + 1)) (p ^ v)) :
    ∃ (hc he : ℕ)
      (Gc : ℕ → Type v) (_ : ∀ v, CommRing (Gc v)) (_ : ∀ v, HopfAlgebra (ZMod p) (Gc v))
      (_ : ∀ v, Coalgebra.IsCocomm (ZMod p) (Gc v)) (_ : ∀ v, Module.Finite (ZMod p) (Gc v))
      (Ge : ℕ → Type v) (_ : ∀ v, CommRing (Ge v)) (_ : ∀ v, HopfAlgebra (ZMod p) (Ge v))
      (_ : ∀ v, Coalgebra.IsCocomm (ZMod p) (Ge v)) (_ : ∀ v, Module.Finite (ZMod p) (Ge v))
      (sc : ∀ v, Gc (v + 1) →ₐc[ZMod p] Gc v) (se : ∀ v, Ge (v + 1) →ₐc[ZMod p] Ge v)
      (qc : ∀ v, G v →ₐc[ZMod p] Gc v) (πe : ∀ v, G v →ₐc[ZMod p] Ge v)
      (σ : ∀ v, Ge v →ₐc[ZMod p] G v)
      (Θ : ∀ v, G v →ₐc[ZMod p] Gc v ⊗[ZMod p] Ge v),
      hc + he = h ∧
      (∀ v, IsLocalRing (Gc v)) ∧ (∀ v, IsReduced (Ge v)) ∧
      (∀ v, Algebra.FormallyUnramified (ZMod p) (Ge v)) ∧
      (∀ v, Function.Surjective (sc v)) ∧
      (∀ v, Module.finrank (ZMod p) (Gc v) = p ^ (v * hc)) ∧
      (∀ v, RingHom.ker (sc v) = PDivisibleGroup.Hopf.torsionIdeal (ZMod p) (Gc (v + 1)) (p ^ v)) ∧
      (∀ v, Function.Surjective (se v)) ∧
      (∀ v, Module.finrank (ZMod p) (Ge v) = p ^ (v * he)) ∧
      (∀ v, RingHom.ker (se v) = PDivisibleGroup.Hopf.torsionIdeal (ZMod p) (Ge (v + 1)) (p ^ v)) ∧
      (∀ v, Function.Surjective (qc v)) ∧ (∀ v, Function.Surjective (πe v)) ∧
      (∀ v, RingHom.ker (πe v : G v →ₐ[ZMod p] Ge v) = nilradical (G v)) ∧
      (∀ v, (πe v).comp (σ v) = BialgHom.id (ZMod p) (Ge v)) ∧
      (∀ v, RingHom.ker (qc v : G v →ₐ[ZMod p] Gc v) =
        Ideal.map (σ v : Ge v →ₐ[ZMod p] G v)
          (RingHom.ker (Bialgebra.counitAlgHom (ZMod p) (Ge v)))) ∧
      (∀ v, Function.Bijective (Θ v)) ∧
      (∀ v b, Θ v b = Algebra.TensorProduct.map (qc v : G v →ₐ[ZMod p] Gc v)
        (πe v : G v →ₐ[ZMod p] Ge v) (Coalgebra.comul (R := ZMod p) b)) ∧
      (∀ v, (qc v).comp (s v) = (sc v).comp (qc (v + 1))) ∧
      (∀ v, (πe v).comp (s v) = (se v).comp (πe (v + 1))) ∧
      (∀ v, (s v).comp (σ (v + 1)) = (σ v).comp (se v)) ∧
      (∀ v, (Θ v).comp (s v) = (Bialgebra.TensorProduct.map (sc v) (se v)).comp (Θ (v + 1))) :=
  S42Tower.main h G s hs hrankG hkerG (fun v => Classical.choice (S42Tower.SplitDatum.nonempty p (G v)))

end S_PDivisibleGroup_exists_tower_isLocalRing_isReduced_bijective_tensorProduct_comul_zmodp
end P2MW
export P2MW.S_PDivisibleGroup_exists_tower_isLocalRing_isReduced_bijective_tensorProduct_comul_zmodp (solution)
