-- Prove2me | solution 1 for RH.Transport.PhysicalHigh.actual_plain_inputs
-- status  : ACCEPTED   (prove)
-- author  : @Himan
-- created : 2026-11-15T04:45:03.547124+00:00
-- url     : https://prove2.me/submissions/a5fff9e9-d7b2-4bcb-93f0-1bc72facacb2

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B028
import Definitions.Def_Transport_PhysicalHigh_EnergyMesh
import Definitions.Def_Transport_PhysicalHigh_PositiveFineSourceInput
import Theorems.Thm_OAI_SevenEighths_CenteredMomentEnergyCertifiedExistence_terminal_certificate
set_option autoImplicit false

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.QuadraticSieve.InitialBound
namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid

open scoped BigOperators Classical SchwartzMap
namespace QuadraticInitialBound
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson

theorem diagonalControl_nonneg (W : 𝓢(ℝ, ℂ)) : 0 ≤ diagonalControl W := by
  unfold diagonalControl
  positivity

open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson
open ConcretePrimeRowBridge ShortDraftHeckeBridge

end QuadraticInitialBound

open scoped Classical FourierTransform SchwartzMap ContDiff
open MeasureTheory

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.FiniteProfileExceptionalNormalize
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentFiniteProfileExceptional
open HeckeFamily CenteredMomentHeckeTwist

theorem sourceControl_nonneg (S) (W : 𝓢(ℝ,ℂ)) : 0≤ sourceControl S W := apply_nonneg _ _

end SevenEighths.CenteredMomentFiniteProfileExceptional

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.FiniteProfileExceptionalPair
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentFiniteProfileExceptional
open HeckeFamily CenteredMomentEligibleEnergy CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentAllocatedDetectorAmplitude CenteredMomentExceptionalAmplitudePair
open CenteredMomentExceptionalAllocationShell ConcretePrimeRowBridge
local notation "O" => HeckeFamily.O
universe u

lemma Profiles.control_nonneg {lo hi:ℝ} (p:Profiles lo hi) (R:Finset (ℕ×ℕ)) : 0≤p.control R :=
  mul_nonneg (sourceControl_nonneg _ _) (sourceControl_nonneg _ _)

variable {lo hi:ℝ}

end SevenEighths.CenteredMomentFiniteProfileExceptional

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.NaturalFixedRaySourceInternal
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentNaturalFixedRaySource
open HeckeFamily CenteredExceptionalProfile CenteredExceptionalCount
open HeckeRowClosure CanonicalRowCompletion ConcretePrimeRowBridge
open CenteredMomentNaturalRowSource UniqueFactorizationMonoid
local notation "O" => HeckeFamily.O

lemma internalQ_ne_zero (Q : Ideal O) (hQ : Q≠0) (η₀ : Character) : internalQ Q η₀≠0 :=
  Ideal.inf_ne_bot_of_ne_bot hQ η₀.modulus_ne_bot

lemma internalQ_ne_top (Q : Ideal O) (hQ : Q≠⊤) (η₀ : Character) : internalQ Q η₀≠⊤ := by
  intro h
  exact hQ (top_le_iff.mp (h ▸ (inf_le_left : internalQ Q η₀≤Q)))

variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

end SevenEighths.CenteredMomentNaturalFixedRaySource

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.NaturalFixedRaySourceFixedIdeal
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentNaturalFixedRaySource
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily
open CenteredMomentDetectorDictionary CenteredMomentNaturalRowSource
open CenteredExceptionalProfile CenteredMomentSecondHeightFamily ConcretePrimeRowBridge
local notation "O" => HeckeFamily.O

variable {Δ : ℝ} {D : Parameters.HighData Δ}

lemma sourceFixedIdeal_ne_zero (F : ProbeFinalAssembly.SourceData D) : sourceFixedIdeal F≠0 :=
  Ideal.inf_ne_bot_of_ne_bot (NeZero.ne F.modulus)
    (Ideal.span_singleton_eq_bot.not.mpr (by norm_num : (72:O)≠0))

lemma sourceFixedIdeal_ne_top (F : ProbeFinalAssembly.SourceData D) : sourceFixedIdeal F≠⊤ := by
  have hmem : Ideal.span {goodLambda}∈F.S := by
    apply F.exclusions.bad
    change Ideal.span {goodLambda}∈({Ideal.span {goodLambda},Ideal.span {(2:O)}} : Finset (Ideal O))
    simp
  have hle : F.modulus≤Ideal.span {goodLambda} := by
    apply Ideal.dvd_iff_le.mp
    exact Finset.dvd_prod_of_mem (fun P : Ideal O=>P) hmem
  have hprime := (F.maximal _ hmem).isPrime
  intro h
  exact hprime.ne_top (top_le_iff.mp (h ▸ (inf_le_left.trans hle : sourceFixedIdeal F≤Ideal.span {goodLambda})))

lemma sourceFixedIdeal_le_modulus (F : ProbeFinalAssembly.SourceData D) : sourceFixedIdeal F≤F.modulus := inf_le_left
lemma sourceFixedIdeal_le_72 (F : ProbeFinalAssembly.SourceData D) : sourceFixedIdeal F≤Ideal.span {(72:O)} := inf_le_right

end SevenEighths.CenteredMomentNaturalFixedRaySource

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.DetectorEnergyInitialState
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap Topology
open Filter

namespace SevenEighths.CenteredMomentDetectorEnergyInitialState
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily
open CenteredMomentEnergyState CenteredMomentRadialEligibleEnergy
open CenteredMomentSecondHeightFamily CenteredExceptionalProfile
open CenteredMomentNaturalFixedRaySource ConcretePrimeRowBridge
open CenteredMomentDetectorPlainFiberSource CenteredMomentDetectorDictionary
open CenteredMomentFiniteProfileExceptional
local notation "O"=>HeckeFamily.O

variable {Δ:ℝ}{D:Parameters.HighData Δ}

lemma source_fixed_gates (F:ProbeFinalAssembly.SourceData D)(η:Character):
    internalQ (sourceFixedIdeal F) η≠0 ∧
    internalQ (sourceFixedIdeal F) η≤F.modulus ∧
    internalQ (sourceFixedIdeal F) η≤η.modulus ∧
    internalQ (sourceFixedIdeal F) η≤Ideal.span {(72:O)}:=
  ⟨internalQ_ne_zero _ (sourceFixedIdeal_ne_zero F) η,
    inf_le_left.trans (sourceFixedIdeal_le_modulus F),inf_le_right,
    inf_le_left.trans (sourceFixedIdeal_le_72 F)⟩

end SevenEighths.CenteredMomentDetectorEnergyInitialState

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.DetectorPlainUnmarkedField
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.ProbeDetectorPlainUnmarkedField
open HeckeDyadic HeckeRowClosure HeckeInverseAmplification
open CenteredMomentDetectorPlainFiberSource
open HeckeFamily HeckeDetectorRawFiber HeckeDetectorBatch ProbeHighRowFamily
open HeckeDetectorRowwisePolynomial HeckeDetectorDyadicProfiles
open CenteredMomentDetectorDictionary CenteredMomentDetectorEnergyInitialState
open CenteredMomentDetectorPlainExceptional CenteredMomentDetectorPlainUnmarkedState
open CenteredMomentDetectorPlainMomentParameters
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentNaturalFixedRaySource
open QuadraticInitialBound
local notation "O" => HeckeFamily.O

theorem radialSupportUpper_spec : 0< radialSupportUpper ∧
    Function.support (radialMajorant:ℝ→ℂ)⊆Set.Iic radialSupportUpper :=
  Classical.choose_spec radialMajorant_support_bound

variable {Δ:ℝ}

end SevenEighths.ProbeDetectorPlainUnmarkedField

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.FinalAssemblyMomentMono
namespace OAI

noncomputable section
open scoped Classical BigOperators
open Set
namespace SevenEighths.ProbeFinalAssembly
open HeckeFamily HeckeInverseAmplification HeckeDetectorRawFiber HeckeDetectorBatch
open ProbeHighRowFamily

lemma rawMoment_mono_constant {data : RowData} {W : ℝ→ℂ} {c κ C D : ℝ}
    (h : RawMoment data W c κ C) (hCD : C≤D) : RawMoment data W c κ D := by
  intro H X hH hX hsize rows hrows
  apply (h H X hH hX hsize rows hrows).trans
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCD (by linarith)) (by positivity)

end SevenEighths.ProbeFinalAssembly

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Energy.BandMonotonicity
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyBandMonotonicity
open HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentFiniteProfileExceptional CenteredMomentInductionEnergy QuadraticInitialBound
local notation "O"=>HeckeFamily.O

lemma profile_control_mono {a b:ℝ}(p:Profiles a b){S T:Finset (ℕ×ℕ)}(hst:S⊆T):
    p.control S≤p.control T:=by
  unfold Profiles.control
  exact mul_le_mul (Seminorm.le_def.mp (Finset.sup_mono hst) (p.profile 0))
    (Seminorm.le_def.mp (Finset.sup_mono hst) (p.profile 1))
    (sourceControl_nonneg _ _) (sourceControl_nonneg _ _)

theorem zeroAt_transport (Q:Ideal O)(a b radial mask L Mcap eps Z:ℝ)
    (a' b' radial' mask' L' Mcap' eps':ℝ)
    (J J':ℕ)(S T:Finset (ℕ×ℕ))(C C':ℝ)
    (hZ:1≤Z)(ha:a≤a')(hb:b'≤b)(hr:radial'≤ radial)(hm:mask'≤ mask)
    (hL:L'≤L)(hM:Mcap'≤Mcap)(he:eps≤eps')(hJ:J≤J')(hS:S⊆T)
    (hC:0≤C)(hCC:C≤C')
    (h:ZeroAt Q a b radial mask L Mcap eps Z J S C):
    ZeroAt Q a' b' radial' mask' L' Mcap' eps' Z J' T C':=by
  intro s hQ hwidth p t X₁ X₂ hX₁ hX₂ hcap₁ hcap₂
  have hcap:Z^L'≤Z^L:=Real.rpow_le_rpow_of_exponent_le hZ hL
  have hh:=h (widenState s hm hr) hQ (hwidth.trans hM) (widenProfiles p ha hb)
    t X₁ X₂ hX₁ hX₂ (hcap₁.trans hcap) (hcap₂.trans hcap)
  change s.plainEnergy p t X₁ X₂≤C*diagonalControl s.radial.profile*(p.control S)^2*
    (1+‖t‖)^J*Z^(s.width+eps) at hh
  have hp:=profile_control_mono p hS
  have hp0:=p.control_nonneg S
  have hd:=diagonalControl_nonneg s.radial.profile
  have ht:(1+‖t‖)^J≤(1+‖t‖)^J':=pow_le_pow_right₀ (by linarith [norm_nonneg t]) hJ
  have hz:Z^(s.width+eps)≤Z^(s.width+eps'):=Real.rpow_le_rpow_of_exponent_le hZ (by linarith)
  have hCnew:0≤C':=hC.trans hCC
  apply hh.trans
  gcongr

variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

local instance instFiniteQuotientOIdeal_solutions_r8dd581_1 : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
omit [Fintype α] [DecidableEq α] in
theorem positiveAt_transport (W:ℝ→ℂ)(bslot a b radial mask L Lslot lo hi Mcap eps κ Z:ℝ)
    (a' b' radial' mask' L' Mcap' eps':ℝ)
    (η₀:Character)(Q:Ideal O)(J J':ℕ)(S T:Finset (ℕ×ℕ))(C C':ℝ)
    (hZ:1≤Z)(ha:a≤a')(hb:b'≤b)(hr:radial'≤ radial)(hm:mask'≤ mask)
    (hL:L'≤L)(hM:Mcap'≤Mcap)(he:eps≤eps')(hJ:J≤J')(hS:S⊆T)
    (hC:0≤C)(hCC:C≤C')
    (h:PositiveAt (α:=α) M H hH W bslot a b radial mask L Lslot lo hi Mcap eps κ Z η₀ Q J S C):
    PositiveAt (α:=α) M H hH W bslot a' b' radial' mask' L' Lslot lo hi Mcap' eps' κ Z η₀ Q J' T C':=by
  intro A θ w σ freq t height hw hwL hσlo hσhi hheight hfreq s hQ hwidth
    p X₁ X₂ hX₁ hX₂ hcap₁ hcap₂ hcapacity
  have hcap:Z^L'≤Z^L:=Real.rpow_le_rpow_of_exponent_le hZ hL
  have hh:=h A θ w σ freq t height hw hwL hσlo hσhi hheight hfreq
    (widenState s hm hr) hQ (hwidth.trans hM) (widenProfiles p ha hb)
    X₁ X₂ hX₁ hX₂ (hcap₁.trans hcap) (hcap₂.trans hcap) hcapacity
  change _≤C*diagonalControl s.radial.profile*(p.control S)^2*
    (1+|t|+height)^J*Z^(s.width+eps) at hh
  have hp:=profile_control_mono p hS
  have hp0:=p.control_nonneg S
  have hd:=diagonalControl_nonneg s.radial.profile
  have ht:(1+|t|+height)^J≤(1+|t|+height)^J':=
    pow_le_pow_right₀ (by linarith [abs_nonneg t]) hJ
  have hz:Z^(s.width+eps)≤Z^(s.width+eps'):=Real.rpow_le_rpow_of_exponent_le hZ (by linarith)
  have hCnew:0≤C':=hC.trans hCC
  apply hh.trans
  gcongr

end SevenEighths.CenteredMomentEnergyBandMonotonicity

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.FirstSecondLossParameters
namespace OAI

noncomputable section

namespace SevenEighths.CenteredMomentFirstSecondLossParameters

lemma depth_covers (Mcap σ:ℝ)(hσ:0<σ):Mcap<(depth Mcap σ:ℝ)*σ/2 := by
  have hh:=Nat.le_ceil (2*Mcap/σ)
  have hn:2*Mcap≤(⌈2*Mcap/σ⌉₊:ℝ)*σ:=(div_le_iff₀ hσ).mp hh
  simp only [depth,Nat.cast_add,Nat.cast_one]
  nlinarith

end SevenEighths.CenteredMomentFirstSecondLossParameters

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SuccessorPaidParameters
namespace OAI

noncomputable section

namespace SevenEighths.CenteredMomentSuccessorPaidParameters
open CenteredMomentFirstSecondLossParameters

lemma mesh_cost (kappa reserve : ℝ) (hk : 0≤kappa) (hr : 0≤ reserve) :
    kappa*(reserve/(kappa+1))≤ reserve := by
  rw [←mul_div_assoc]
  apply (div_le_iff₀ (by positivity : 0<kappa+1)).mpr
  nlinarith

end SevenEighths.CenteredMomentSuccessorPaidParameters

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Energy.WidthSchedule
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentEnergyWidthSchedule
open CenteredMomentSuccessorPaidParameters CenteredMomentFirstSecondLossParameters

theorem bounds (M B κ ε:ℝ)(hM:0≤M)(hB:0≤B)(hκ:0≤κ)(hε:0<ε):
    0<amplification ε ∧ amplification ε≤1 ∧ amplification ε≤ε/16000 ∧
    0< reserve M B ε ∧ 0< mesh M B κ ε ∧ mesh M B κ ε≤ reserve M B ε ∧
    κ*mesh M B κ ε≤ reserve M B ε ∧
    20*reserve M B ε≤amplification ε/2 ∧
    M<width M B ε (count M ε) ∧
    loss M B ε (count M ε)≤ε/1000 :=by
  have hs:0<amplification ε:=lt_min (by norm_num) (by positivity)
  have hs1:amplification ε≤1:=min_le_left _ _
  have hse:amplification ε≤ε/16000:=min_le_right _ _
  have hn:0≤(count M ε:ℝ):=Nat.cast_nonneg _
  have hL:0<scale M B ε:=by unfold scale;positivity
  have hr:0< reserve M B ε:=lt_min (by positivity) (by positivity)
  have hrs:reserve M B ε≤amplification ε/100:=min_le_left _ _
  have hre:reserve M B ε≤ε/(1000000*scale M B ε):=min_le_right _ _
  have hp:reserve M B ε*(1000000*scale M B ε)≤ε:=
    (le_div_iff₀ (by positivity)).mp hre
  have hnL:(count M ε:ℝ)≤ scale M B ε:=by unfold scale;linarith
  have h1L:1≤ scale M B ε:=by unfold scale;linarith
  have hnR:(count M ε:ℝ)*reserve M B ε≤ε/1000000:=by
    have hh:=mul_le_mul_of_nonneg_right hnL hr.le
    nlinarith
  have hR:reserve M B ε≤ε/1000000:=by
    have hh:=mul_le_mul_of_nonneg_right h1L hr.le
    nlinarith
  have hm:0< mesh M B κ ε:=by unfold mesh;positivity
  have hmr:mesh M B κ ε≤ reserve M B ε:=by
    unfold mesh
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith
  have hkm:κ*mesh M B κ ε≤ reserve M B ε:=mesh_cost κ _ hκ hr.le
  have hw:M<width M B ε (count M ε):=by
    have hd:=depth_covers M (amplification ε) hs
    change M<(count M ε:ℝ)*amplification ε/2 at hd
    unfold width
    linarith
  refine ⟨hs,hs1,hse,hr,hm,hmr,hkm,by linarith,hw,?_⟩
  unfold loss
  linarith

lemma loss_le_final (M B κ ε:ℝ)(hM:0≤M)(hB:0≤B)(hκ:0≤κ)(hε:0<ε)
    (k:ℕ)(hk:k≤ count M ε):loss M B ε k≤ε/1000:=by
  have hb:=bounds M B κ ε hM hB hκ hε
  have hr:=hb.2.2.2.1
  have hk':(k:ℝ)≤(count M ε:ℝ):=by exact_mod_cast hk
  apply le_trans _ hb.2.2.2.2.2.2.2.2.2
  unfold loss
  gcongr

end SevenEighths.CenteredMomentEnergyWidthSchedule

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Energy.StageReserveSchedule
namespace OAI

noncomputable section

namespace SevenEighths.CenteredMomentEnergyStageReserveSchedule
open CenteredMomentEnergyWidthSchedule CenteredMomentSuccessorPaidParameters

lemma stageLoss_final (M B κ ε:ℝ)(hM:0≤M)(hB:0≤B)(hκ:0≤κ)(hε:0<ε)
    (k:ℕ)(hk:k≤ count M ε):stageLoss M B ε k≤ε/500:=by
  have hh:=loss_le_final M B κ ε hM hB hκ hε k hk
  unfold stageLoss
  linarith

end SevenEighths.CenteredMomentEnergyStageReserveSchedule

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Energy.WidthRanges
namespace OAI

noncomputable section

namespace SevenEighths.CenteredMomentEnergyWidthRanges
open CenteredMomentEnergyProfiles CenteredMomentEnergyWidthSchedule

lemma range_nonneg (M B L:ℝ)(hM:0≤M)(hB:0≤B)(n:ℕ):0≤ range M B L n:=by
  induction n with
  | zero=>exact zero_le_one.trans (le_max_left _ _)
  | succ n ih=>simp only [range,step];positivity

lemma sourceCap_nonneg (M B L:ℝ)(hM:0≤M)(hB:0≤B)(n:ℕ):0≤ sourceCap M B L n:=by
  have hr:=range_nonneg M B L hM hB n
  unfold sourceCap
  positivity

end SevenEighths.CenteredMomentEnergyWidthRanges

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Energy.CappedWidthInduction
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter

namespace SevenEighths.CenteredMomentEnergyCappedWidthInduction
open HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyWidthSchedule CenteredMomentEnergyWidthRanges
open CenteredMomentEnergyStageReserveSchedule CenteredMomentEnergyBandMonotonicity
open CenteredMomentFiniteProfileExceptional
open CenteredMomentNaturalFixedRaySource
local notation "O"=>HeckeFamily.O

open CenteredMomentEnergyWidthInduction (remaining lowerAt lengthAt )

lemma bandWidth_terminal (M B ε:ℝ)(hM:0≤M)(hB:0≤B)(hε:0<ε):
    bandWidth M B ε (count M ε)=M:=by
  have hh: M<width M B ε (count M ε):=
    (bounds M B 0 ε hM hB (by norm_num) hε).2.2.2.2.2.2.2.2.1
  exact min_eq_left hh.le

variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

local instance instFiniteQuotientOIdeal_solutions_r8dd581_2 : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
omit [Fintype α] [DecidableEq α] in
theorem certified_terminal (W:ℝ→ℂ)(bslot a b radial Bmask L lo hi Mcap κ ε:ℝ)
    (hmask:0≤Bmask)(hMcap:0≤Mcap)(hκ0:0≤κ)(hε:0<ε)
    (h:CertifiedBand (α:=α) M H hH W bslot a b radial Bmask L lo hi Mcap κ ε (count Mcap ε)):
    ∃degree:ℕ,∃S:Finset (ℕ×ℕ),∀η₀:Character,∀Q:Ideal O,Q≤M→
      internalQ Q η₀≠0→internalQ Q η₀≠⊤→internalQ Q η₀≤Ideal.span {(72:O)}→
      ∃Czero Cpositive:ℝ,0<Czero ∧ 0<Cpositive ∧
      ∀ᶠZ:ℝ in atTop,1<Z ∧
        ZeroAt (internalQ Q η₀) a b radial Bmask L Mcap ε Z degree S Czero ∧
        PositiveAt (α:=α) M H hH W bslot a b radial Bmask L
          (fineMesh Mcap Bmask L κ ε) lo hi Mcap ε κ Z η₀ Q degree S Cpositive:=by
  let Bs:=finalSourceCap Mcap Bmask L ε
  have hBs:0≤Bs:=sourceCap_nonneg Mcap Bmask L hMcap hmask _
  obtain ⟨hs,hs1,hse,hr,hm,hmm,hκm,h20,hcover,hloss⟩:=bounds Mcap Bs κ ε hMcap hBs hκ0 hε
  have he:stageLoss Mcap Bs ε (count Mcap ε)≤ε:=by
    have hh:=stageLoss_final Mcap Bs κ ε hMcap hBs hκ0 hε (count Mcap ε) le_rfl
    linarith
  obtain ⟨degree,S,hbound⟩:=h
  refine ⟨degree,S,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Czero,Cpositive,hCzero,hCpositive,hcert⟩:=hbound η₀ Q hQM hQ0 hQt hQ72
  refine ⟨Czero,Cpositive,hCzero,hCpositive,?_⟩
  filter_upwards [hcert] with Z hZ
  have hz:=hZ.2.1
  have hp:=hZ.2.2
  simp only [lowerAt,lengthAt,remaining,Nat.sub_self,CenteredMomentEnergyProfiles.lower,range] at hz hp
  have hterminal:=bandWidth_terminal Mcap Bs ε hMcap hBs hε
  change bandWidth Mcap (finalSourceCap Mcap Bmask L ε) ε (count Mcap ε)=Mcap at hterminal
  rw [hterminal] at hz hp
  refine ⟨hZ.1,?_,?_⟩
  · exact zeroAt_transport (internalQ Q η₀) _ _ _ _ _ _ _ Z _ _ _ _ _ _ _
      degree degree S S Czero Czero hZ.1.le le_rfl le_rfl le_rfl le_rfl
      (le_max_right _ _) le_rfl he le_rfl (Finset.Subset.refl _) hCzero.le le_rfl hz
  · exact positiveAt_transport (α:=α) M H hH W bslot _ _ _ _ _ _ _ _ _ _ κ Z
      _ _ _ _ _ _ _ η₀ Q degree degree S S Cpositive Cpositive hZ.1.le
      le_rfl le_rfl le_rfl le_rfl (le_max_right _ _) le_rfl he le_rfl (Finset.Subset.refl _)
      hCpositive.le le_rfl hp

end SevenEighths.CenteredMomentEnergyCappedWidthInduction

end

end OAI
end

section
-- module Transport.PhysicalHigh.PlainEnergy (LW56e2)
namespace RH.Transport.PhysicalHigh

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open OAI OAI.SevenEighths
open HeckeFamily CenteredMomentEnergyCappedWidthInduction
open CenteredMomentEnergyCertifiedExistence CenteredMomentEnergyWidthSchedule

local notation "O" => HeckeFamily.O
variable {Slot : Type*} [Fintype Slot] [DecidableEq Slot]
variable (M : Ideal O) [NeZero M]
local instance plainEnergyQuotient_sol : Finite (O ⧸ M) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

/-- A producer for the actual terminal arithmetic energy band. The theorem
allows every finite number of physical slots and every positive error loss. -/
theorem actual_plain_energy_fixed_kappa
    (W : ℝ → ℂ) (hWs : Function.support W ⊆ Set.Icc 1 2)
    (hW : ContDiff ℝ ∞ W) (radial ε : ℝ) (hrad : 0 < radial) (hε : 0 < ε)
    (hbeta : (51 / 100 : ℝ) ≤ HeckeZeroSupremum.beta)
    (hceiling : HeckeZeroSupremum.beta ≤ 7 / 8) :
    CertifiedBand (α := Slot) M H hH W
      2 (1 / 4) (9 / 4) radial 0 1 (33 / 50) (33 / 50)
      2 (3 / 4) ε (count 2 ε) := by
  exact terminal_certificate (α := Slot) M H hH W
    1 2 (1 / 4) (9 / 4) radial 0 1 (33 / 50) (33 / 50) 2 (3 / 4) ε
    (by norm_num) hWs hW (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) hrad (by norm_num) (by norm_num) (by norm_num) hε hbeta
    (by linarith)

end
end RH.Transport.PhysicalHigh

end

section
-- module Transport.PhysicalHigh.PlainInputExtract (LW56e2)
namespace RH.Transport.PhysicalHigh

noncomputable section
open scoped Classical BigOperators SchwartzMap ComplexConjugate
open Filter

open OAI OAI.SevenEighths
open HeckeFamily HeckeDyadic HeckeInverseAmplification HeckeDetectorRawFiber HeckeDetectorBatch
open ProbeFinalAssembly ProbeHighRowFamily Parameters
open CenteredMomentEnergyBands CenteredMomentEnergyState
open CenteredMomentEnergyCappedWidthInduction CenteredMomentEnergyWidthRanges
open CenteredMomentEnergyWidthSchedule CenteredMomentDetectorPlainMomentParameters
open CenteredMomentDetectorEnergyInitialState CenteredMomentNaturalFixedRaySource
open ProbeDetectorPlainUnmarkedField
local notation "O"=>HeckeFamily.O

theorem plain_inputs {Δ:ℝ}{D:HighData Δ}(F:SourceData D)
    (N:ℕ)(εm:ℝ)(hεm:0< εm)
    (hcert:∀bΦ:ℝ,0< bΦ→CertifiedBand (α:=Fin N) F.modulus ⊤ le_top
      (fun x=>conj (F.W x)) 2 (1/4) (9/4) bΦ 0 1 (33/50) (33/50) 2
      (3/4) (εm/4) (count 2 (εm/4))):
    PositiveFineSourceInput F N εm (plainMesh εm) ∧
    (∃degree:ℕ,∃control:Finset (ℕ×ℕ),∀η₀:Character,∃A:ℝ,0< A ∧ ∀ᶠU:ℝ in atTop,
      ZeroAt (internalQ (sourceFixedIdeal F) η₀) (1/4) (9/4) radialSupportUpper
        0 1 2 (εm/4) U degree control A):=by
  have ht (bΦ:ℝ)(hbΦ:0< bΦ):=
    certified_terminal F.modulus ⊤ le_top (fun x=>conj (F.W x))
      2 (1/4) (9/4) bΦ 0 1 (33/50) (33/50) 2 (3/4) (εm/4)
      (by norm_num) (by norm_num) (by norm_num) (by positivity) (hcert bΦ hbΦ)
  have hactual (bΦ:ℝ)(hbΦ:0< bΦ):
      ∃degree:ℕ,∃control:Finset (ℕ×ℕ),∀η₀:Character,
      ∃Czero Cpositive:ℝ,0< Czero ∧ 0< Cpositive ∧ ∀ᶠU:ℝ in atTop,
      ZeroAt (internalQ (sourceFixedIdeal F) η₀) (1/4) (9/4) bΦ 0 1 2
        (εm/4) U degree control Czero ∧
      PositiveAt (α:=Fin N) F.modulus ⊤ le_top (fun x=>conj (F.W x))
        2 (1/4) (9/4) bΦ 0 1 (plainMesh εm) (33/50) (33/50) 2
        (εm/4) (3/4) U η₀ (sourceFixedIdeal F) degree control Cpositive:=by
    obtain ⟨degree,control,hbound⟩:=ht bΦ hbΦ
    refine ⟨degree,control,?_⟩
    intro η₀
    obtain ⟨Cz,Cp,hCz,hCp,hbound⟩:=hbound η₀ (sourceFixedIdeal F)
      (sourceFixedIdeal_le_modulus F) (source_fixed_gates F η₀).1
      (internalQ_ne_top _ (sourceFixedIdeal_ne_top F) η₀) (source_fixed_gates F η₀).2.2.2
    exact ⟨Cz,Cp,hCz,hCp,hbound.mono (fun U h=>⟨h.2.1,h.2.2⟩)⟩
  constructor
  · intro bΦ hbΦ
    obtain ⟨degree,control,h⟩:=hactual bΦ hbΦ
    refine ⟨degree,control,?_⟩
    intro η₀
    obtain ⟨Cz,Cp,hCz,hCp,h⟩:=h η₀
    exact ⟨Cp,hCp,h.mono (fun U h=>h.2)⟩
  · obtain ⟨degree,control,h⟩:=hactual radialSupportUpper radialSupportUpper_spec.1
    refine ⟨degree,control,?_⟩
    intro η₀
    obtain ⟨Cz,Cp,hCz,hCp,h⟩:=h η₀
    exact ⟨Cz,hCz,h.mono (fun U h=>h.1)⟩

end
end RH.Transport.PhysicalHigh

end

open RH RH.Transport RH.Transport.PhysicalHigh
open scoped Classical BigOperators
open Filter
open OAI OAI.SevenEighths
open HeckeFamily HeckeInverseAmplification ProbeFinalAssembly ProbeHighRowFamily
open Parameters
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentDetectorEnergyInitialState
open CenteredMomentNaturalFixedRaySource
open ProbeDetectorPlainUnmarkedField
noncomputable section
open scoped ComplexConjugate

theorem solution {Δ:ℝ}{D:HighData Δ}(F:SourceData D)
    (N:ℕ)(εm:ℝ)(hεm:0<εm)
    (hbeta:(51/100:ℝ)≤HeckeZeroSupremum.beta)
    (hceiling:HeckeZeroSupremum.beta≤7/8):
    PositiveFineSourceInput F N εm (plainMesh εm) ∧
    (∃degree:ℕ,∃control:Finset (ℕ×ℕ),∀η₀:Character,∃A:ℝ,0<A ∧ ∀ᶠU:ℝ in atTop,
      ZeroAt (internalQ (sourceFixedIdeal F) η₀) (1/4) (9/4) radialSupportUpper
        0 1 2 (εm/4) U degree control A):=by
  apply RH.Transport.PhysicalHigh.plain_inputs F N εm hεm
  intro bΦ hbΦ
  exact RH.Transport.PhysicalHigh.actual_plain_energy_fixed_kappa (Slot:=Fin N) F.modulus ⊤ le_top
    (fun x=>conj (F.W x)) (by intro x hx; exact F.complex_support (by simpa using hx))
    (Complex.conjCLE.contDiff.comp (F.W.smooth ⊤)) bΦ (εm/4) hbΦ (by positivity)
    hbeta hceiling
