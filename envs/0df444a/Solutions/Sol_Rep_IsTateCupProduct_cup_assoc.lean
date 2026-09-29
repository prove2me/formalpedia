-- Prove2me | solution 1 for Rep.IsTateCupProduct.cup_assoc
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/28657cb0-4e1f-5ce1-9a9b-3b1ddb949867

import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import Definitions.Def_GroupCohomology_TateSeam
import Definitions.Def_GroupCohomology_TateShiftMaps
import Definitions.Def_GroupCohomology_CochainCup
import Definitions.Def_GroupCohomology_IsGradedCupProduct
import Definitions.Def_GroupCohomology_IsTateCupProduct
import Definitions.Def_GroupCohomology_TateDimensionShift
import Theorems.Thm_Rep_dimShiftDown_shortExact
import Theorems.Thm_Rep_dimShiftUp_shortExact
import Theorems.Thm_Rep_bijective_tateDelta_of_isZero
import Theorems.Thm_Rep_bijective_tateDelta_dimShiftUp
import Theorems.Thm_Rep_isZero_tateCohomology_indBot_tensor
import Theorems.Thm_Rep_isZero_tateCohomology_tensor_indBot
import Theorems.Thm_Rep_shortExact_dimShiftDown_map_tensorRight
import Theorems.Thm_Rep_shortExact_dimShiftDown_map_tensorLeft
import Theorems.Thm_Rep_shortExact_map_tensorRight_of_splitting
import Theorems.Thm_Rep_shortExact_map_tensorLeft_of_splitting
import Theorems.Thm_Rep_indBotr_indBotIota
import Theorems.Thm_Rep_indBotPi_indBotSigma
import Theorems.Thm_Rep_tateDelta_naturality
import Theorems.Thm_Rep_nonempty_tateCohomology_iso_of_iso
import Theorems.Thm_Rep_IsTateCupProduct_cup_mk_mk
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Rep_IsTateCupProduct_cup_assoc

set_option autoImplicit false
universe u
p2m_open "CategoryTheory Rep CategoryTheory.MonoidalCategory"

namespace P2mS26Assoc

noncomputable section

variable {k G : Type u} [CommRing k] [Group G]

theorem rTensor_section {X : ShortComplex (Rep.{u} k G)} (s : X.X₃ →ₗ[k] X.X₂) (hs : ∀ x : X.X₃, X.g.hom (s x) = x)
    (B : Rep.{u} k G) (w : (X.map (MonoidalCategory.tensorRight B)).X₃) :
    (X.map (MonoidalCategory.tensorRight B)).g.hom (LinearMap.rTensor B s w) = w := by
  have h1 : X.g.hom.toLinearMap ∘ₗ s = LinearMap.id := LinearMap.ext hs
  have h2 : (X.g ▷ B).hom.toLinearMap ∘ₗ LinearMap.rTensor B s = LinearMap.id := by
    rw [Rep.hom_whiskerRight, Representation.IntertwiningMap.toLinearMap_rTensor, ← LinearMap.rTensor_comp, h1,
      LinearMap.rTensor_id]
  exact LinearMap.congr_fun h2 w

theorem lTensor_section {X : ShortComplex (Rep.{u} k G)} (s : X.X₃ →ₗ[k] X.X₂) (hs : ∀ x : X.X₃, X.g.hom (s x) = x)
    (A : Rep.{u} k G) (w : (X.map (MonoidalCategory.tensorLeft A)).X₃) :
    (X.map (MonoidalCategory.tensorLeft A)).g.hom (LinearMap.lTensor A s w) = w := by
  have h1 : X.g.hom.toLinearMap ∘ₗ s = LinearMap.id := LinearMap.ext hs
  have h2 : (A ◁ X.g).hom.toLinearMap ∘ₗ LinearMap.lTensor A s = LinearMap.id := by
    rw [Rep.hom_whiskerLeft, Representation.IntertwiningMap.toLinearMap_lTensor, ← LinearMap.lTensor_comp, h1,
      LinearMap.lTensor_id]
  exact LinearMap.congr_fun h2 w

theorem se_down_R (A B : Rep.{u} k G) : (A.dimShiftDown.map (tensorRight B)).ShortExact :=
  Rep.shortExact_dimShiftDown_map_tensorRight A B
theorem se_down_RR (A B C : Rep.{u} k G) : ((A.dimShiftDown.map (tensorRight B)).map (tensorRight C)).ShortExact :=
  Rep.shortExact_map_tensorRight_of_splitting (se_down_R A B) (LinearMap.rTensor B A.indBotσ)
    (rTensor_section (X := A.dimShiftDown) A.indBotσ (Rep.indBotPi_indBotSigma A) B) C
theorem se_down_L (A B : Rep.{u} k G) : (B.dimShiftDown.map (tensorLeft A)).ShortExact :=
  Rep.shortExact_dimShiftDown_map_tensorLeft A B
theorem se_down_LR (A B C : Rep.{u} k G) : ((B.dimShiftDown.map (tensorLeft A)).map (tensorRight C)).ShortExact :=
  Rep.shortExact_map_tensorRight_of_splitting (se_down_L A B) (LinearMap.lTensor A B.indBotσ)
    (lTensor_section (X := B.dimShiftDown) B.indBotσ (Rep.indBotPi_indBotSigma B) A) C
theorem se_down_RL (A B C : Rep.{u} k G) : ((B.dimShiftDown.map (tensorRight C)).map (tensorLeft A)).ShortExact :=
  Rep.shortExact_map_tensorLeft_of_splitting (se_down_R B C) (LinearMap.rTensor C B.indBotσ)
    (rTensor_section (X := B.dimShiftDown) B.indBotσ (Rep.indBotPi_indBotSigma B) C) A
theorem se_down_LL (A B C : Rep.{u} k G) : ((C.dimShiftDown.map (tensorLeft B)).map (tensorLeft A)).ShortExact :=
  Rep.shortExact_map_tensorLeft_of_splitting (se_down_L B C) (LinearMap.lTensor B C.indBotσ)
    (lTensor_section (X := C.dimShiftDown) C.indBotσ (Rep.indBotPi_indBotSigma C) B) A

variable [Fintype G]

def upSection (A : Rep.{u} k G) : A.dimShiftUpObj →ₗ[k] A.indBot :=
  (LinearMap.range (Rep.indBotι A).hom.toLinearMap).liftQ
    (LinearMap.id - (Rep.indBotι A).hom.toLinearMap ∘ₗ A.indBotr) (by
      rintro _ ⟨a, rfl⟩
      rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.id_apply,
        Representation.IntertwiningMap.toLinearMap_apply, Rep.indBotr_indBotIota]
      exact sub_self _)

theorem g_upSection (A : Rep.{u} k G) (x : A.dimShiftUpObj) : A.dimShiftUp.g.hom (upSection A x) = x := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  change Submodule.Quotient.mk (x - (Rep.indBotι A).hom (A.indBotr x)) = Submodule.Quotient.mk x
  rw [Submodule.Quotient.mk_sub, sub_eq_self, Submodule.Quotient.mk_eq_zero]
  exact ⟨A.indBotr x, rfl⟩

theorem se_up_R (A B : Rep.{u} k G) : (A.dimShiftUp.map (tensorRight B)).ShortExact :=
  Rep.shortExact_map_tensorRight_of_splitting (Rep.dimShiftUp_shortExact A) (upSection A) (g_upSection A) B
theorem se_up_L (A B : Rep.{u} k G) : (B.dimShiftUp.map (tensorLeft A)).ShortExact :=
  Rep.shortExact_map_tensorLeft_of_splitting (Rep.dimShiftUp_shortExact B) (upSection B) (g_upSection B) A
theorem se_up_RR (A B C : Rep.{u} k G) : ((A.dimShiftUp.map (tensorRight B)).map (tensorRight C)).ShortExact :=
  Rep.shortExact_map_tensorRight_of_splitting (se_up_R A B) (LinearMap.rTensor B (upSection A))
    (rTensor_section (X := A.dimShiftUp) (upSection A) (g_upSection A) B) C
theorem se_up_LR (A B C : Rep.{u} k G) : ((B.dimShiftUp.map (tensorLeft A)).map (tensorRight C)).ShortExact :=
  Rep.shortExact_map_tensorRight_of_splitting (se_up_L A B) (LinearMap.lTensor A (upSection B))
    (lTensor_section (X := B.dimShiftUp) (upSection B) (g_upSection B) A) C
theorem se_up_RL (A B C : Rep.{u} k G) : ((B.dimShiftUp.map (tensorRight C)).map (tensorLeft A)).ShortExact :=
  Rep.shortExact_map_tensorLeft_of_splitting (se_up_R B C) (LinearMap.rTensor C (upSection B))
    (rTensor_section (X := B.dimShiftUp) (upSection B) (g_upSection B) C) A
theorem se_up_LL (A B C : Rep.{u} k G) : ((C.dimShiftUp.map (tensorLeft B)).map (tensorLeft A)).ShortExact :=
  Rep.shortExact_map_tensorLeft_of_splitting (se_up_L B C) (LinearMap.lTensor B (upSection C))
    (lTensor_section (X := C.dimShiftUp) (upSection C) (g_upSection C) B) A

omit [Fintype G] in

def αNatL (X : ShortComplex (Rep.{u} k G)) (B C : Rep.{u} k G) :
    X.map (tensorRight (B ⊗ C)) ⟶ (X.map (tensorRight B)).map (tensorRight C) where
  τ₁ := (α_ X.X₁ B C).inv
  τ₂ := (α_ X.X₂ B C).inv
  τ₃ := (α_ X.X₃ B C).inv
  comm₁₂ := (MonoidalCategory.associator_inv_naturality_left X.f B C).symm
  comm₂₃ := (MonoidalCategory.associator_inv_naturality_left X.g B C).symm

omit [Fintype G] in

def αNatM (X : ShortComplex (Rep.{u} k G)) (A C : Rep.{u} k G) :
    (X.map (tensorRight C)).map (tensorLeft A) ⟶ (X.map (tensorLeft A)).map (tensorRight C) where
  τ₁ := (α_ A X.X₁ C).inv
  τ₂ := (α_ A X.X₂ C).inv
  τ₃ := (α_ A X.X₃ C).inv
  comm₁₂ := (MonoidalCategory.associator_inv_naturality_middle A X.f C).symm
  comm₂₃ := (MonoidalCategory.associator_inv_naturality_middle A X.g C).symm

omit [Fintype G] in

def αNatR (X : ShortComplex (Rep.{u} k G)) (A B : Rep.{u} k G) :
    (X.map (tensorLeft B)).map (tensorLeft A) ⟶ X.map (tensorLeft (A ⊗ B)) where
  τ₁ := (α_ A B X.X₁).inv
  τ₂ := (α_ A B X.X₂).inv
  τ₃ := (α_ A B X.X₃).inv
  comm₁₂ := (MonoidalCategory.associator_inv_naturality_right A B X.f).symm
  comm₂₃ := (MonoidalCategory.associator_inv_naturality_right A B X.g).symm

theorem natAt {X Y : ShortComplex (Rep.{u} k G)} (hX : X.ShortExact) (hY : Y.ShortExact) (τ : X ⟶ Y) (n : ℤ)
    (y : X.X₃.tateCohomology n) :
    (Rep.tateMap τ.τ₁ (n + 1)).hom ((Rep.tateδ hX n).hom y) = (Rep.tateδ hY n).hom ((Rep.tateMap τ.τ₃ n).hom y) := by
  have := congrArg (fun f => f.hom y) (Rep.tateDelta_naturality hX hY τ n)
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using this

theorem isZero_of_iso {X Y : Rep.{u} k G} (e : X ≅ Y) (n : ℤ) (h : Limits.IsZero (Y.tateCohomology n)) :
    Limits.IsZero (X.tateCohomology n) :=
  h.of_iso (Rep.nonempty_tateCohomology_iso_of_iso e n).some

omit [Fintype G] in
theorem eps_mul_self (p : ℤ) : ((p.negOnePow : ℤ) : k) * ((p.negOnePow : ℤ) : k) = 1 := by
  rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]

omit [Fintype G] in
theorem eps_add (p q : ℤ) : (((p + q).negOnePow : ℤ) : k) = ((p.negOnePow : ℤ) : k) * ((q.negOnePow : ℤ) : k) := by
  rw [Int.negOnePow_add, Units.val_mul, Int.cast_mul]

omit [Fintype G] in
theorem eps_smul_eps_smul {M : Type u} [AddCommGroup M] [Module k M] (p : ℤ) (v : M) :
    ((p.negOnePow : ℤ) : k) • ((p.negOnePow : ℤ) : k) • v = v := by
  rw [smul_smul, eps_mul_self, one_smul]

omit [Fintype G] in
theorem eps_eps_cancel {M : Type u} [AddCommGroup M] [Module k M] (p q : ℤ) (v : M) :
    (((p.negOnePow : ℤ) : k) * ((q.negOnePow : ℤ) : k)) • ((p.negOnePow : ℤ) : k) • ((q.negOnePow : ℤ) : k) • v = v := by
  rw [smul_smul, smul_smul, show ((p.negOnePow : ℤ) : k) * ((q.negOnePow : ℤ) : k) * ((p.negOnePow : ℤ) : k)
      * ((q.negOnePow : ℤ) : k) = (((p.negOnePow : ℤ) : k) * ((p.negOnePow : ℤ) : k))
        * (((q.negOnePow : ℤ) : k) * ((q.negOnePow : ℤ) : k)) by ring,
    eps_mul_self, eps_mul_self, one_mul, one_smul]

theorem smul_cup_left (cup : Rep.TateCupFamily k G) (A B : Rep.{u} k G) (p q r : ℤ) (h : p + q = r) (c : k)
    (v : A.tateCohomology p) (w : B.tateCohomology q) : cup A B p q r h (c • v) w = c • cup A B p q r h v w := by
  rw [map_smul, LinearMap.smul_apply]

def P (cup : Rep.TateCupFamily k G) (p q r : ℤ) : Prop :=
  ∀ (A B C : Rep.{u} k G) (r₁₂ r₂₃ r₁₂₃ : ℤ) (h₁₂ : p + q = r₁₂) (h₂₃ : q + r = r₂₃) (h : r₁₂ + r = r₁₂₃)
    (x : A.tateCohomology p) (y : B.tateCohomology q) (z : C.tateCohomology r),
    cup (A ⊗ B) C r₁₂ r r₁₂₃ h (cup A B p q r₁₂ h₁₂ x y) z
      = (Rep.tateMap (α_ A B C).inv r₁₂₃).hom (cup A (B ⊗ C) p r₂₃ r₁₂₃ (by omega) x (cup B C q r r₂₃ h₂₃ y z))

theorem zInd {Q : ℤ → Prop} (h0 : Q 0) (hup : ∀ n, Q n → Q (n + 1)) (hdown : ∀ n, Q (n + 1) → Q n) (n : ℤ) : Q n := by
  induction n using Int.induction_on with
  | zero => exact h0
  | succ i ih => exact hup _ ih
  | pred i ih => exact hdown _ (by rwa [sub_add_cancel])

def tinv (A B : Rep.{u} k G) (a : A.ρ.invariants) (b : B.ρ.invariants) : (A ⊗ B).ρ.invariants :=
  ⟨(a : A) ⊗ₜ[k] (b : B), fun g => by
    change (A.ρ.tprod B.ρ) g ((a : A) ⊗ₜ[k] (b : B)) = (a : A) ⊗ₜ[k] (b : B)
    rw [Representation.tprod_apply, TensorProduct.map_tmul, a.2 g, b.2 g]⟩

variable {cup : Rep.TateCupFamily k G}

theorem base (hcup : Rep.IsTateCupProduct cup) : P cup 0 0 0 := by
  intro A B C r₁₂ r₂₃ r₁₂₃ h₁₂ h₂₃ h x y z
  obtain rfl : r₁₂ = 0 := by omega
  obtain rfl : r₂₃ = 0 := by omega
  obtain rfl : r₁₂₃ = 0 := by omega
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  refine ((congrArg (fun w => cup (A ⊗ B) C 0 0 0 h w (Submodule.Quotient.mk c))
    (hcup.cup_mk_mk A B a b (tinv A B a b) rfl)).trans
      ((hcup.cup_mk_mk (A ⊗ B) C (tinv A B a b) c (tinv (A ⊗ B) C (tinv A B a b) c) rfl).trans ?_))
  refine Eq.trans ?_ (congrArg (fun w => (Rep.tateMap (α_ A B C).inv 0).hom w)
    ((congrArg (fun w => cup A (B ⊗ C) 0 0 0 (by omega) (Submodule.Quotient.mk a) w)
      (hcup.cup_mk_mk B C b c (tinv B C b c) rfl)).trans
        (hcup.cup_mk_mk A (B ⊗ C) a (tinv B C b c) (tinv A (B ⊗ C) a (tinv B C b c)) rfl)).symm)
  change (Submodule.Quotient.mk (tinv (A ⊗ B) C (tinv A B a b) c) : ((A ⊗ B) ⊗ C).tateH0)
    = Submodule.Quotient.mk (Rep.invariantsMap (α_ A B C).inv (tinv A (B ⊗ C) a (tinv B C b c)))
  exact congrArg _ (Subtype.ext rfl)

theorem downP (hcup : Rep.IsTateCupProduct cup) (p q r : ℤ) (ih : P cup (p + 1) q r) : P cup p q r := by
  intro A B C r₁₂ r₂₃ r₁₂₃ h₁₂ h₂₃ h x y z
  have hX := Rep.dimShiftDown_shortExact A
  have hXB := se_down_R A B
  have hXBC := se_down_RR A B C
  have hX_BC := se_down_R A (B ⊗ C)
  have h0 : ∀ n : ℤ, Limits.IsZero (((A.dimShiftDown.map (tensorRight B)).map (tensorRight C)).X₂.tateCohomology n) :=
    fun n => isZero_of_iso (α_ A.indBot B C) n (Rep.isZero_tateCohomology_indBot_tensor A (B ⊗ C) n)
  refine (Rep.bijective_tateDelta_of_isZero hXBC r₁₂₃ (h0 r₁₂₃) (h0 (r₁₂₃ + 1))).1 ?_
  refine ((hcup.delta_cup hXB C hXBC r₁₂ r r₁₂₃ h (cup A B p q r₁₂ h₁₂ x y) z).trans
    ((congrArg (fun w => cup _ C (r₁₂ + 1) r (r₁₂₃ + 1) (by omega) w z) (hcup.delta_cup hX B hXB p q r₁₂ h₁₂ x y)).trans
      (ih _ B C (r₁₂ + 1) r₂₃ (r₁₂₃ + 1) (by omega) h₂₃ (by omega) ((Rep.tateδ hX p).hom x) y z))).trans ?_
  exact ((congrArg (fun w => (Rep.tateMap (αNatL A.dimShiftDown B C).τ₁ (r₁₂₃ + 1)).hom w)
      (hcup.delta_cup hX (B ⊗ C) hX_BC p r₂₃ r₁₂₃ (by omega) x (cup B C q r r₂₃ h₂₃ y z))).symm.trans
    (natAt hX_BC hXBC (αNatL A.dimShiftDown B C) r₁₂₃ (cup A (B ⊗ C) p r₂₃ r₁₂₃ (by omega) x (cup B C q r r₂₃ h₂₃ y z))))

theorem downQ (hcup : Rep.IsTateCupProduct cup) (p q r : ℤ) (ih : P cup p (q + 1) r) : P cup p q r := by
  intro A B C r₁₂ r₂₃ r₁₂₃ h₁₂ h₂₃ h x y z
  have hX := Rep.dimShiftDown_shortExact B
  have hAX := se_down_L A B
  have hAXC := se_down_LR A B C
  have hXC := se_down_R B C
  have hA_XC := se_down_RL A B C
  have h0 : ∀ n : ℤ, Limits.IsZero (((B.dimShiftDown.map (tensorLeft A)).map (tensorRight C)).X₂.tateCohomology n) :=
    fun n => isZero_of_iso (whiskerRightIso (β_ A B.indBot) C ≪≫ α_ B.indBot A C) n
      (Rep.isZero_tateCohomology_indBot_tensor B (A ⊗ C) n)
  refine (Rep.bijective_tateDelta_of_isZero hAXC r₁₂₃ (h0 r₁₂₃) (h0 (r₁₂₃ + 1))).1 ?_
  set ε : k := ((p.negOnePow : ℤ) : k) with hε
  have hsm : ∀ v : (A ⊗ B.dimShiftDown.X₁).tateCohomology (r₁₂ + 1),
      cup _ C (r₁₂ + 1) r (r₁₂₃ + 1) (by omega) (ε • v) z = ε • cup _ C (r₁₂ + 1) r (r₁₂₃ + 1) (by omega) v z :=
    fun v => by rw [map_smul, LinearMap.smul_apply]

  have E1 := (hcup.delta_cup hAX C hAXC r₁₂ r r₁₂₃ h (cup A B p q r₁₂ h₁₂ x y) z).trans
    ((congrArg (fun w => cup _ C (r₁₂ + 1) r (r₁₂₃ + 1) (by omega) w z) (hcup.cup_delta A hX hAX p q r₁₂ h₁₂ x y)).trans
      ((hsm _).trans (congrArg (fun t => ε • t)
        (ih A _ C (r₁₂ + 1) (r₂₃ + 1) (r₁₂₃ + 1) (by omega) (by omega) (by omega) x ((Rep.tateδ hX q).hom y) z))))

  have E2 := natAt hA_XC hAXC (αNatM B.dimShiftDown A C) r₁₂₃
    (cup A (B ⊗ C) p r₂₃ r₁₂₃ (by omega) x (cup B C q r r₂₃ h₂₃ y z))
  have E3 := congrArg (fun v => (Rep.tateMap (αNatM B.dimShiftDown A C).τ₁ (r₁₂₃ + 1)).hom v)
    ((hcup.cup_delta A hXC hA_XC p r₂₃ r₁₂₃ (by omega) x (cup B C q r r₂₃ h₂₃ y z)).trans
      (congrArg (fun t => ε • cup A _ p (r₂₃ + 1) (r₁₂₃ + 1) (by omega) x t) (hcup.delta_cup hX C hXC q r r₂₃ h₂₃ y z)))
  have E4 := (Rep.tateMap (αNatM B.dimShiftDown A C).τ₁ (r₁₂₃ + 1)).hom.map_smul ε
    (cup A _ p (r₂₃ + 1) (r₁₂₃ + 1) (by omega) x
      (cup B.dimShiftDown.X₁ C (q + 1) r (r₂₃ + 1) (by omega) ((Rep.tateδ hX q).hom y) z))
  exact E1.trans ((E4.symm.trans E3.symm).trans E2)

theorem downR (hcup : Rep.IsTateCupProduct cup) (p q r : ℤ) (ih : P cup p q (r + 1)) : P cup p q r := by
  intro A B C r₁₂ r₂₃ r₁₂₃ h₁₂ h₂₃ h x y z
  have hX := Rep.dimShiftDown_shortExact C
  have hABX := se_down_L (A ⊗ B) C
  have hBX := se_down_L B C
  have hA_BX := se_down_LL A B C
  have h0 : ∀ n : ℤ, Limits.IsZero ((C.dimShiftDown.map (tensorLeft (A ⊗ B))).X₂.tateCohomology n) :=
    fun n => Rep.isZero_tateCohomology_tensor_indBot (A ⊗ B) C n
  refine (Rep.bijective_tateDelta_of_isZero hABX r₁₂₃ (h0 r₁₂₃) (h0 (r₁₂₃ + 1))).1 ?_
  have hε : ((r₁₂.negOnePow : ℤ) : k) = ((p.negOnePow : ℤ) : k) * ((q.negOnePow : ℤ) : k) := by rw [← h₁₂, eps_add]

  have E1 : (Rep.tateδ hABX r₁₂₃).hom (cup (A ⊗ B) C r₁₂ r r₁₂₃ h (cup A B p q r₁₂ h₁₂ x y) z)
      = ((p.negOnePow : ℤ) : k) • ((q.negOnePow : ℤ) : k) •
          (Rep.tateMap (α_ A B C.dimShiftDown.X₁).inv (r₁₂₃ + 1)).hom
            (cup A (B ⊗ C.dimShiftDown.X₁) p (r₂₃ + 1) (r₁₂₃ + 1) (by omega) x
              (cup B C.dimShiftDown.X₁ q (r + 1) (r₂₃ + 1) (by omega) y ((Rep.tateδ hX r).hom z))) :=
    (hcup.cup_delta (A ⊗ B) hX hABX r₁₂ r r₁₂₃ h (cup A B p q r₁₂ h₁₂ x y) z).trans
      ((congrArg (fun t => ((r₁₂.negOnePow : ℤ) : k) • t)
        (ih A B _ r₁₂ (r₂₃ + 1) (r₁₂₃ + 1) h₁₂ (by omega) (by omega) x y ((Rep.tateδ hX r).hom z))).trans
        ((congrArg (fun e : k => e • _) hε).trans (mul_smul _ _ _)))

  have E2 := natAt hA_BX hABX (αNatR C.dimShiftDown A B) r₁₂₃
    (cup A (B ⊗ C) p r₂₃ r₁₂₃ (by omega) x (cup B C q r r₂₃ h₂₃ y z))
  have E3 : (Rep.tateδ hA_BX r₁₂₃).hom (cup A (B ⊗ C) p r₂₃ r₁₂₃ (by omega) x (cup B C q r r₂₃ h₂₃ y z))
      = ((p.negOnePow : ℤ) : k) • ((q.negOnePow : ℤ) : k) •
          cup A (B ⊗ C.dimShiftDown.X₁) p (r₂₃ + 1) (r₁₂₃ + 1) (by omega) x
            (cup B C.dimShiftDown.X₁ q (r + 1) (r₂₃ + 1) (by omega) y ((Rep.tateδ hX r).hom z)) :=
    (hcup.cup_delta A hBX hA_BX p r₂₃ r₁₂₃ (by omega) x (cup B C q r r₂₃ h₂₃ y z)).trans
      ((congrArg (fun t => ((p.negOnePow : ℤ) : k) • cup A _ p (r₂₃ + 1) (r₁₂₃ + 1) (by omega) x t)
        (hcup.cup_delta B hX hBX q r r₂₃ h₂₃ y z)).trans
        (congrArg (fun t => ((p.negOnePow : ℤ) : k) • t)
          (map_smul (cup A _ p (r₂₃ + 1) (r₁₂₃ + 1) (by omega) x) ((q.negOnePow : ℤ) : k) _)))
  have E4 : (Rep.tateMap (αNatR C.dimShiftDown A B).τ₁ (r₁₂₃ + 1)).hom
      (((p.negOnePow : ℤ) : k) • ((q.negOnePow : ℤ) : k) •
        cup A (B ⊗ C.dimShiftDown.X₁) p (r₂₃ + 1) (r₁₂₃ + 1) (by omega) x
          (cup B C.dimShiftDown.X₁ q (r + 1) (r₂₃ + 1) (by omega) y ((Rep.tateδ hX r).hom z)))
      = ((p.negOnePow : ℤ) : k) • ((q.negOnePow : ℤ) : k) •
          (Rep.tateMap (αNatR C.dimShiftDown A B).τ₁ (r₁₂₃ + 1)).hom
            (cup A (B ⊗ C.dimShiftDown.X₁) p (r₂₃ + 1) (r₁₂₃ + 1) (by omega) x
              (cup B C.dimShiftDown.X₁ q (r + 1) (r₂₃ + 1) (by omega) y ((Rep.tateδ hX r).hom z))) :=
    (map_smul (Rep.tateMap (αNatR C.dimShiftDown A B).τ₁ (r₁₂₃ + 1)).hom ((p.negOnePow : ℤ) : k) _).trans
      (congrArg (fun t => ((p.negOnePow : ℤ) : k) • t)
        (map_smul (Rep.tateMap (αNatR C.dimShiftDown A B).τ₁ (r₁₂₃ + 1)).hom ((q.negOnePow : ℤ) : k) _))
  exact E1.trans ((E4.symm.trans
    (congrArg (fun v => (Rep.tateMap (αNatR C.dimShiftDown A B).τ₁ (r₁₂₃ + 1)).hom v) E3).symm).trans E2)

theorem upP (hcup : Rep.IsTateCupProduct cup) (p q r : ℤ) (ih : P cup p q r) : P cup (p + 1) q r := by
  intro A B C r₁₂ r₂₃ r₁₂₃ h₁₂ h₂₃ h x y z
  have hX := Rep.dimShiftUp_shortExact A
  obtain ⟨x, rfl⟩ := (Rep.bijective_tateDelta_dimShiftUp A hX p).2 x
  obtain ⟨r₁₂, rfl⟩ : ∃ s, r₁₂ = s + 1 := ⟨r₁₂ - 1, by omega⟩
  obtain ⟨r₁₂₃, rfl⟩ : ∃ s, r₁₂₃ = s + 1 := ⟨r₁₂₃ - 1, by omega⟩
  have hXB := se_up_R A B
  have hXBC := se_up_RR A B C
  have hX_BC := se_up_R A (B ⊗ C)
  exact ((congrArg (fun w => cup _ C (r₁₂ + 1) r (r₁₂₃ + 1) h w z) (hcup.delta_cup hX B hXB p q r₁₂ (by omega) x y)).symm.trans
    ((hcup.delta_cup hXB C hXBC r₁₂ r r₁₂₃ (by omega) (cup _ B p q r₁₂ (by omega) x y) z).symm.trans
      ((congrArg (fun w => (Rep.tateδ hXBC r₁₂₃).hom w) (ih _ B C r₁₂ r₂₃ r₁₂₃ (by omega) h₂₃ (by omega) x y z)).trans
        ((natAt hX_BC hXBC (αNatL A.dimShiftUp B C) r₁₂₃
          (cup _ (B ⊗ C) p r₂₃ r₁₂₃ (by omega) x (cup B C q r r₂₃ h₂₃ y z))).symm.trans
          (congrArg (fun w => (Rep.tateMap (αNatL A.dimShiftUp B C).τ₁ (r₁₂₃ + 1)).hom w)
            (hcup.delta_cup hX (B ⊗ C) hX_BC p r₂₃ r₁₂₃ (by omega) x (cup B C q r r₂₃ h₂₃ y z)))))))

theorem upQ (hcup : Rep.IsTateCupProduct cup) (p q r : ℤ) (ih : P cup p q r) : P cup p (q + 1) r := by
  intro A B C r₁₂ r₂₃ r₁₂₃ h₁₂ h₂₃ h x y z
  have hX := Rep.dimShiftUp_shortExact B
  obtain ⟨y, rfl⟩ := (Rep.bijective_tateDelta_dimShiftUp B hX q).2 y
  obtain ⟨r₁₂, rfl⟩ : ∃ s, r₁₂ = s + 1 := ⟨r₁₂ - 1, by omega⟩
  obtain ⟨r₂₃, rfl⟩ : ∃ s, r₂₃ = s + 1 := ⟨r₂₃ - 1, by omega⟩
  obtain ⟨r₁₂₃, rfl⟩ : ∃ s, r₁₂₃ = s + 1 := ⟨r₁₂₃ - 1, by omega⟩
  have hAX := se_up_L A B
  have hAXC := se_up_LR A B C
  have hXC := se_up_R B C
  have hA_XC := se_up_RL A B C

  have E1 : cup A B p (q + 1) (r₁₂ + 1) h₁₂ x ((Rep.tateδ hX q).hom y)
      = ((p.negOnePow : ℤ) : k) • (Rep.tateδ hAX r₁₂).hom (cup A B.dimShiftUp.X₃ p q r₁₂ (by omega) x y) :=
    (eps_smul_eps_smul p _).symm.trans (congrArg (fun t => ((p.negOnePow : ℤ) : k) • t)
      (hcup.cup_delta A hX hAX p q r₁₂ (by omega) x y).symm)
  have E2 : cup (A ⊗ B) C (r₁₂ + 1) r (r₁₂₃ + 1) h (cup A B p (q + 1) (r₁₂ + 1) h₁₂ x ((Rep.tateδ hX q).hom y)) z
      = ((p.negOnePow : ℤ) : k) • (Rep.tateMap (αNatM B.dimShiftUp A C).τ₁ (r₁₂₃ + 1)).hom
          ((Rep.tateδ hA_XC r₁₂₃).hom (cup A (B.dimShiftUp.X₃ ⊗ C) p r₂₃ r₁₂₃ (by omega) x
            (cup B.dimShiftUp.X₃ C q r r₂₃ (by omega) y z))) :=
    (congrArg (fun w => cup (A ⊗ B) C (r₁₂ + 1) r (r₁₂₃ + 1) h w z) E1).trans
      ((smul_cup_left cup _ C (r₁₂ + 1) r (r₁₂₃ + 1) h _ _ z).trans (congrArg (fun t => ((p.negOnePow : ℤ) : k) • t)
        ((hcup.delta_cup hAX C hAXC r₁₂ r r₁₂₃ (by omega) (cup A B.dimShiftUp.X₃ p q r₁₂ (by omega) x y) z).symm.trans
          ((congrArg (fun w => (Rep.tateδ hAXC r₁₂₃).hom w)
            (ih A B.dimShiftUp.X₃ C r₁₂ r₂₃ r₁₂₃ (by omega) (by omega) (by omega) x y z)).trans
            (natAt hA_XC hAXC (αNatM B.dimShiftUp A C) r₁₂₃
              (cup A (B.dimShiftUp.X₃ ⊗ C) p r₂₃ r₁₂₃ (by omega) x (cup B.dimShiftUp.X₃ C q r r₂₃ (by omega) y z))).symm))))
  have E3 : (Rep.tateδ hA_XC r₁₂₃).hom (cup A (B.dimShiftUp.X₃ ⊗ C) p r₂₃ r₁₂₃ (by omega) x
        (cup B.dimShiftUp.X₃ C q r r₂₃ (by omega) y z))
      = ((p.negOnePow : ℤ) : k) • cup A (B ⊗ C) p (r₂₃ + 1) (r₁₂₃ + 1) (by omega) x
          (cup B C (q + 1) r (r₂₃ + 1) h₂₃ ((Rep.tateδ hX q).hom y) z) :=
    (hcup.cup_delta A hXC hA_XC p r₂₃ r₁₂₃ (by omega) x (cup B.dimShiftUp.X₃ C q r r₂₃ (by omega) y z)).trans
      (congrArg (fun t => ((p.negOnePow : ℤ) : k) • cup A _ p (r₂₃ + 1) (r₁₂₃ + 1) (by omega) x t)
        (hcup.delta_cup hX C hXC q r r₂₃ (by omega) y z))
  refine E2.trans ((congrArg (fun t => ((p.negOnePow : ℤ) : k) •
    (Rep.tateMap (αNatM B.dimShiftUp A C).τ₁ (r₁₂₃ + 1)).hom t) E3).trans ?_)
  exact (congrArg (fun t => ((p.negOnePow : ℤ) : k) • t)
    (map_smul (Rep.tateMap (αNatM B.dimShiftUp A C).τ₁ (r₁₂₃ + 1)).hom ((p.negOnePow : ℤ) : k) _)).trans
      (eps_smul_eps_smul p _)

theorem upR (hcup : Rep.IsTateCupProduct cup) (p q r : ℤ) (ih : P cup p q r) : P cup p q (r + 1) := by
  intro A B C r₁₂ r₂₃ r₁₂₃ h₁₂ h₂₃ h x y z
  have hX := Rep.dimShiftUp_shortExact C
  obtain ⟨z, rfl⟩ := (Rep.bijective_tateDelta_dimShiftUp C hX r).2 z
  obtain ⟨r₂₃, rfl⟩ : ∃ s, r₂₃ = s + 1 := ⟨r₂₃ - 1, by omega⟩
  obtain ⟨r₁₂₃, rfl⟩ : ∃ s, r₁₂₃ = s + 1 := ⟨r₁₂₃ - 1, by omega⟩
  have hABX := se_up_L (A ⊗ B) C
  have hBX := se_up_L B C
  have hA_BX := se_up_LL A B C
  have hε : ((r₁₂.negOnePow : ℤ) : k) = ((p.negOnePow : ℤ) : k) * ((q.negOnePow : ℤ) : k) := by rw [← h₁₂, eps_add]
  have E1 : cup (A ⊗ B) C r₁₂ (r + 1) (r₁₂₃ + 1) h (cup A B p q r₁₂ h₁₂ x y) ((Rep.tateδ hX r).hom z)
      = ((r₁₂.negOnePow : ℤ) : k) • (Rep.tateδ hABX r₁₂₃).hom
          (cup (A ⊗ B) C.dimShiftUp.X₃ r₁₂ r r₁₂₃ (by omega) (cup A B p q r₁₂ h₁₂ x y) z) :=
    (eps_smul_eps_smul r₁₂ _).symm.trans (congrArg (fun t => ((r₁₂.negOnePow : ℤ) : k) • t)
      (hcup.cup_delta (A ⊗ B) hX hABX r₁₂ r r₁₂₃ (by omega) (cup A B p q r₁₂ h₁₂ x y) z).symm)
  have E2 : cup (A ⊗ B) C r₁₂ (r + 1) (r₁₂₃ + 1) h (cup A B p q r₁₂ h₁₂ x y) ((Rep.tateδ hX r).hom z)
      = ((r₁₂.negOnePow : ℤ) : k) • (Rep.tateMap (αNatR C.dimShiftUp A B).τ₁ (r₁₂₃ + 1)).hom
          ((Rep.tateδ hA_BX r₁₂₃).hom (cup A (B ⊗ C.dimShiftUp.X₃) p r₂₃ r₁₂₃ (by omega) x
            (cup B C.dimShiftUp.X₃ q r r₂₃ (by omega) y z))) :=
    E1.trans (congrArg (fun t => ((r₁₂.negOnePow : ℤ) : k) • t)
      ((congrArg (fun w => (Rep.tateδ hABX r₁₂₃).hom w)
        (ih A B C.dimShiftUp.X₃ r₁₂ r₂₃ r₁₂₃ h₁₂ (by omega) (by omega) x y z)).trans
        (natAt hA_BX hABX (αNatR C.dimShiftUp A B) r₁₂₃
          (cup A (B ⊗ C.dimShiftUp.X₃) p r₂₃ r₁₂₃ (by omega) x (cup B C.dimShiftUp.X₃ q r r₂₃ (by omega) y z))).symm))
  have E3 : (Rep.tateδ hA_BX r₁₂₃).hom (cup A (B ⊗ C.dimShiftUp.X₃) p r₂₃ r₁₂₃ (by omega) x
        (cup B C.dimShiftUp.X₃ q r r₂₃ (by omega) y z))
      = ((p.negOnePow : ℤ) : k) • ((q.negOnePow : ℤ) : k) • cup A (B ⊗ C) p (r₂₃ + 1) (r₁₂₃ + 1) (by omega) x
          (cup B C q (r + 1) (r₂₃ + 1) h₂₃ y ((Rep.tateδ hX r).hom z)) :=
    (hcup.cup_delta A hBX hA_BX p r₂₃ r₁₂₃ (by omega) x (cup B C.dimShiftUp.X₃ q r r₂₃ (by omega) y z)).trans
      ((congrArg (fun t => ((p.negOnePow : ℤ) : k) • cup A _ p (r₂₃ + 1) (r₁₂₃ + 1) (by omega) x t)
        (hcup.cup_delta B hX hBX q r r₂₃ (by omega) y z)).trans
        (congrArg (fun t => ((p.negOnePow : ℤ) : k) • t)
          (map_smul (cup A _ p (r₂₃ + 1) (r₁₂₃ + 1) (by omega) x) ((q.negOnePow : ℤ) : k) _)))
  refine E2.trans ((congrArg (fun t => ((r₁₂.negOnePow : ℤ) : k) •
    (Rep.tateMap (αNatR C.dimShiftUp A B).τ₁ (r₁₂₃ + 1)).hom t) E3).trans ?_)
  exact (congrArg (fun t => ((r₁₂.negOnePow : ℤ) : k) • t)
    ((map_smul (Rep.tateMap (αNatR C.dimShiftUp A B).τ₁ (r₁₂₃ + 1)).hom ((p.negOnePow : ℤ) : k) _).trans
      (congrArg (fun t => ((p.negOnePow : ℤ) : k) • t)
        (map_smul (Rep.tateMap (αNatR C.dimShiftUp A B).τ₁ (r₁₂₃ + 1)).hom ((q.negOnePow : ℤ) : k) _)))).trans
    ((congrArg (fun e : k => e • _) hε).trans (eps_eps_cancel p q _))

theorem all (hcup : Rep.IsTateCupProduct cup) (p q r : ℤ) : P cup p q r :=
  zInd (Q := fun r => P cup p q r)
    (zInd (Q := fun q => P cup p q 0)
      (zInd (Q := fun p => P cup p 0 0) (base hcup) (fun n hn => upP hcup n 0 0 hn) (fun n hn => downP hcup n 0 0 hn) p)
      (fun n hn => upQ hcup p n 0 hn) (fun n hn => downQ hcup p n 0 hn) q)
    (fun n hn => upR hcup p q n hn) (fun n hn => downR hcup p q n hn) r

end

end P2mS26Assoc

theorem solution {k G : Type u} [CommRing k] [Group G] [Fintype G]
    {cup : Rep.TateCupFamily k G} (hcup : Rep.IsTateCupProduct cup) (A B C : Rep.{u} k G)
    (p q r r₁₂ r₂₃ r₁₂₃ : ℤ) (h₁₂ : p + q = r₁₂) (h₂₃ : q + r = r₂₃) (h : r₁₂ + r = r₁₂₃)
    (x : A.tateCohomology p) (y : B.tateCohomology q) (z : C.tateCohomology r) :
    cup (A ⊗ B) C r₁₂ r r₁₂₃ h (cup A B p q r₁₂ h₁₂ x y) z
      = (Rep.tateMap (α_ A B C).inv r₁₂₃).hom (cup A (B ⊗ C) p r₂₃ r₁₂₃ (by omega) x (cup B C q r r₂₃ h₂₃ y z)) :=
  P2mS26Assoc.all hcup p q r A B C r₁₂ r₂₃ r₁₂₃ h₁₂ h₂₃ h x y z

end S_Rep_IsTateCupProduct_cup_assoc
end P2MW
export P2MW.S_Rep_IsTateCupProduct_cup_assoc (solution)
