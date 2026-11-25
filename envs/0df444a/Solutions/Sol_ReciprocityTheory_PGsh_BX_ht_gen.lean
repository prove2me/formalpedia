-- Prove2me | solution 1 for ReciprocityTheory.PGsh.BX.ht_gen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:28:20.607986+00:00
-- url     : https://prove2.me/submissions/088398b9-5fef-4026-bebe-6b3c0200171d

import Definitions.Def_ReciprocityTheory_DualLattices_InstAddCommMonoidFibreFst
import Definitions.Def_ReciprocityTheory_DualLattices_NilSurjOfSqZero
import Definitions.Def_ReciprocityTheory_DualLattices_NsmulTensorEqZero
import Theorems.Thm_ReciprocityTheory_PGsh_BX_pmap_congr_hom
import Theorems.Thm_ReciprocityTheory_PGsh_BX_nsmul_tensor_eq_zero
import Theorems.Thm_ReciprocityTheory_PGsh_BX_nsmul_of_same_red
import Theorems.Thm_ReciprocityTheory_PGsh_BX_exists_lift_red
import Theorems.Thm_ReciprocityTheory_PGsh_BX_HtC_congr
import Theorems.Thm_P2M_ReciprocityTheory_PGsh_DualPair___comp_fr_8c3b9426a108
import Theorems.Thm_P2M_ReciprocityTheory_PGsh_DualPair_fr___2154160be0da
import Theorems.Thm_P2M_ReciprocityTheory_PGsh_DualPair_fr_comp___e46f679c4983
import Theorems.Thm_ReciprocityTheory_PGsh_BX_fibreFst_nsmul_mk
import Theorems.Thm_ReciprocityTheory_PGsh_BX_nsmul1_hcongr
import Theorems.Thm_ReciprocityTheory_PGsh_BX_nsmul1_smul
import Theorems.Thm_ReciprocityTheory_PGsh_BX_nsmul1_zero1
import Theorems.Thm_ReciprocityTheory_PGsh_BX_nsmul2_hcongr
import Theorems.Thm_ReciprocityTheory_PGsh_BX_nsmul2_smul
import Theorems.Thm_ReciprocityTheory_PGsh_BX_pmap_nsmul1
import Theorems.Thm_ReciprocityTheory_PGsh_BX_pmap_nsmul2
import Theorems.Thm_ReciprocityTheory_PGsh_BX_smul_hcongr
import Theorems.Thm_ReciprocityTheory_PGsh_DualPair_natCast_D
import Theorems.Thm_ReciprocityTheory_PGsh_FP_ext
import Theorems.Thm_ReciprocityTheory_PGsh_evalT_add
import Theorems.Thm_ReciprocityTheory_PGsh_evalT_mem
import Theorems.Thm_ReciprocityTheory_PGsh_evalT_tmul
import Theorems.Thm_ReciprocityTheory_PGsh_evalT_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct
open ReciprocityTheory ReciprocityTheory.PGsh
universe u
variable {R₀ : Type u} [CommRing R₀]
open ReciprocityTheory.PGsh.BX
variable (B : BX R₀) {R : LAlg R₀} (Dp : DualPair R)
namespace ReciprocityTheory.PGsh.BX
theorem _root_.solution (hB2 : HighestWeightVectorUniformBounds B) (N : ℕ) (hN : (N : (R : Type u)) = 0) (y : B.G R)
    (h : B.gg →ₗ[R₀] R) (hh : B.IsHeight Dp N y h) (Y : B.gg ⊗[R₀] Dp.π.ker)
    (w₀ : B.P Dp.D (B.tg Dp.π Dp.sqZero Y) (B.map Dp.σ y))
    (hu : HEq (B.pmap Dp.π w₀) (B.zero1 y)) :
    HEq (B.nsmul1 w₀ N) (B.zero1 (B.map Dp.σ y)) ∧
    ∃ c : (Dp.D : Type u)ˣ,
      (c : (Dp.D : Type u)) = 1 - evalT (Dp.σ.1.toLinearMap ∘ₗ h) Dp.π.ker Y ∧
      HEq (B.nsmul2 w₀ N) (B.smul c (B.zero2 (B.tg Dp.π Dp.sqZero Y))) := by

  have pmap_heq : ∀ {S : LAlg R₀} (f : LHom Dp.D S) {a a' b b' : B.G Dp.D} (ha : a = a') (hb : b = b')
      {w : B.P Dp.D a b} {w' : B.P Dp.D a' b'}, HEq w w' → HEq (B.pmap f w) (B.pmap f w') := by
    intro S f a a' b b' ha hb w w' hw
    subst ha hb
    rw [eq_of_heq hw]
  have tr1h : ∀ {a a' b : B.G Dp.D} (e : a = a') (w : B.P Dp.D a b), HEq (B.tr1 e w) w := by
    intro a a' b e w
    subst e
    rfl
  have tr2h : ∀ {a b b' : B.G Dp.D} (e : b = b') (w : B.P Dp.D a b), HEq (B.tr2 e w) w := by
    intro a b b' e w
    subst e
    rfl
  have tr1s : ∀ {a a' b : B.G Dp.D} (e : a = a') (l : (Dp.D : Type u)ˣ) (w : B.P Dp.D a b),
      B.tr1 e (B.smul l w) = B.smul l (B.tr1 e w) := by
    intro a a' b e l w
    subst e
    rfl
  have tr2s : ∀ {a b b' : B.G Dp.D} (e : b = b') (l : (Dp.D : Type u)ˣ) (w : B.P Dp.D a b),
      B.tr2 e (B.smul l w) = B.smul l (B.tr2 e w) := by
    intro a b b' e l w
    subst e
    rfl
  have hπσ : B.map Dp.π (B.map Dp.σ y) = y := by
    rw [← B.map_comp]
    have : Dp.π.comp Dp.σ = LHom.id R := Subtype.ext (AlgHom.ext fun r => Dp.sect r)
    rw [this, B.map_id]
  have hker : ∀ Y' : B.gg ⊗[R₀] Dp.π.ker, B.map Dp.π (B.tg Dp.π Dp.sqZero Y') = 0 :=
    fun Y' => (B.tg_ker _ _ _).mpr ⟨Y', rfl⟩
  have hNx : ∀ Y' : B.gg ⊗[R₀] Dp.π.ker, N • B.tg Dp.π Dp.sqZero Y' = 0 := by
    intro Y'
    rw [← map_nsmul, B.nsmul_tensor_eq_zero (Dp.natCast_D hN) _ Y', map_zero]
  have hNy : N • B.map Dp.σ y = 0 := by
    obtain ⟨z, ⟨_, hy', _⟩, _⟩ := hh 0
    exact hy'
  have hEmem : ∀ Y' : B.gg ⊗[R₀] Dp.π.ker,
      evalT (Dp.σ.1.toLinearMap ∘ₗ h) Dp.π.ker Y' ∈ RingHom.ker Dp.π.1 :=
    fun Y' => evalT_mem _ (RingHom.ker Dp.π.1) Y'

  have claim : ∀ Y' : B.gg ⊗[R₀] Dp.π.ker,
      B.HtC Dp N y (B.tg Dp.π Dp.sqZero Y') (evalT (Dp.σ.1.toLinearMap ∘ₗ h) Dp.π.ker Y') := by
    intro Y'
    induction Y' using TensorProduct.induction_on with
    | zero =>
      refine B.HtC_congr Dp (map_zero _).symm (evalT_zero _ _).symm ?_
      refine ⟨B.zero1 (B.map Dp.σ y), ?_, B.nsmul1_zero1 _ N, 1, by simp, ?_⟩
      · refine (B.zeroFst_nat Dp.π _).trans ?_
        rw [hπσ]
      · refine (B.nsmul2_zero1 _ N).trans ?_
        rw [hNy, B.zeroFst_zero, B.one_smul]
    | tmul g k =>
      obtain ⟨z, ⟨hx1, hy1, u, l₁, l₂, e1, e2, hz⟩, hzv⟩ := hh g
      obtain ⟨u', hu'⟩ := B.exists_lift_red Dp (hker _) hπσ (B.zero1 y)
      have hB1 := (hB2 R Dp N hN).1 y g u' hu'
      obtain ⟨m, hm⟩ := B.exists_smul u u'
      have e1' : B.tr1 hx1 (B.nsmul1 u' N) = B.zero1 (B.map Dp.σ y) :=
        eq_of_heq ((tr1h hx1 _).trans hB1)
      rw [← hm, B.nsmul1_smul, tr1s, e1, ← B.mul_smul] at e1'
      have hml : m ^ N * l₁ = 1 := B.smul_eq_self e1'
      have hl1 : l₁ = (m ^ N)⁻¹ := eq_inv_of_mul_eq_one_right hml
      have e2' : B.tr2 hy1 (B.nsmul2 u' N) = B.smul (m ^ N * l₂) (B.zero2 _) := by
        rw [← hm, B.nsmul2_smul, tr2s, e2, ← B.mul_smul]
      have hc0 : m ^ N * l₂ = z⁻¹ := by
        rw [hz, hl1, div_eq_mul_inv, mul_inv, inv_inv, inv_inv]
      have hzinv : ((z⁻¹ : (Dp.D : Type u)ˣ) : (Dp.D : Type u)) = 1 - Dp.σ.1 (h g) * Dp.η := by
        have hmul : (z : (Dp.D : Type u)) * (1 - Dp.σ.1 (h g) * Dp.η) = 1 := by
          rw [hzv]
          linear_combination -(Dp.σ.1 (h g) * Dp.σ.1 (h g)) * Dp.η_sq
        calc ((z⁻¹ : (Dp.D : Type u)ˣ) : (Dp.D : Type u))
            = ((z⁻¹ : (Dp.D : Type u)ˣ) : (Dp.D : Type u)) * ((z : (Dp.D : Type u)) * (1 - Dp.σ.1 (h g) * Dp.η)) := by
              rw [hmul, mul_one]
          _ = 1 - Dp.σ.1 (h g) * Dp.η := by rw [← mul_assoc, Units.inv_mul, one_mul]

      set r : (R : Type u) := Dp.κ (k : (Dp.D : Type u)) with hr
      have hk0 : Dp.π.1 (k : (Dp.D : Type u)) = 0 := k.2
      have hk : (k : (Dp.D : Type u)) = Dp.σ.1 r * Dp.η := by
        have := Dp.decomp (k : (Dp.D : Type u))
        rw [hk0, map_zero, zero_add] at this
        exact this
      set f := Dp.fr r with hfdef
      have hfσ : ∀ s : (R : Type u), f.1 (Dp.σ.1 s) = Dp.σ.1 s := by
        intro s
        have := congrArg (fun φ : LHom R Dp.D => φ.1 s) (Dp.fr_comp_σ r)
        exact this
      have hfk : ∀ a ∈ Dp.π.ker, f.1.toLinearMap a ∈ Dp.π.ker := by
        intro a ha
        have h1 := congrArg (fun φ : LHom Dp.D R => φ.1 a) (Dp.π_comp_fr r)
        show Dp.π.1 (f.1 a) = 0
        have h2 : Dp.π.1 a = 0 := ha
        rw [← h2]
        exact h1
      have hfy : B.map f (B.map Dp.σ y) = B.map Dp.σ y := by
        rw [← B.map_comp, Dp.fr_comp_σ]
      have hfx : B.map f (B.tg Dp.π Dp.sqZero (g ⊗ₜ Dp.ηk)) = B.tg Dp.π Dp.sqZero (g ⊗ₜ k) := by
        rw [← B.tg_nat Dp.π Dp.π Dp.sqZero Dp.sqZero f hfk, LinearMap.lTensor_tmul]
        congr 2
        apply Subtype.ext
        show f.1 Dp.η = (k : (Dp.D : Type u))
        rw [hk, Dp.fr_η]
      have hxk : B.map Dp.π (B.tg Dp.π Dp.sqZero (g ⊗ₜ Dp.ηk)) = 0 := hker _
      refine ⟨B.tr2 hfy (B.tr1 hfx (B.pmap f u')), ?_, ?_, Units.map (f.1 : (Dp.D : Type u) →* (Dp.D : Type u)) z⁻¹, ?_, ?_⟩
      ·
        have h1 : HEq (B.pmap Dp.π (B.tr2 hfy (B.tr1 hfx (B.pmap f u')))) (B.pmap Dp.π (B.pmap f u')) :=
          pmap_heq Dp.π hfx.symm hfy.symm ((tr2h hfy _).trans (tr1h hfx _))
        refine h1.trans ((B.pmap_comp f Dp.π u').symm.trans ?_)
        exact (B.pmap_congr_hom (Dp.π_comp_fr r) u').trans hu'
      ·
        have h1 : HEq (B.nsmul1 (B.tr2 hfy (B.tr1 hfx (B.pmap f u'))) N) (B.nsmul1 (B.pmap f u') N) :=
          B.nsmul1_hcongr hfx.symm hfy.symm N ((tr2h hfy _).trans (tr1h hfx _))
        refine h1.trans ((B.pmap_nsmul1 f u' N).symm.trans ?_)
        refine (pmap_heq f hx1 rfl hB1).trans ((B.zeroFst_nat f _).trans ?_)
        rw [hfy]
      ·
        rw [Units.coe_map, MonoidHom.coe_coe, hzinv, evalT_tmul, map_sub, map_one, map_mul, hfσ, Dp.fr_η, hk]
        try simp only [LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply]
        try ring
      ·
        have h1 : HEq (B.nsmul2 (B.tr2 hfy (B.tr1 hfx (B.pmap f u'))) N) (B.nsmul2 (B.pmap f u') N) :=
          B.nsmul2_hcongr hfx.symm hfy.symm N ((tr2h hfy _).trans (tr1h hfx _))
        refine h1.trans ((B.pmap_nsmul2 f u' N).symm.trans ?_)
        have h2 : HEq (B.nsmul2 u' N) (B.smul z⁻¹ (B.zero2 (B.tg Dp.π Dp.sqZero (g ⊗ₜ Dp.ηk)))) := by
          rw [← hc0, ← e2']
          exact (tr2h hy1 _).symm
        refine (pmap_heq f rfl hy1 h2).trans ?_
        rw [B.pmap_smul]
        refine B.smul_hcongr hfx (map_zero _) _ ((B.zeroSnd_nat f _).trans ?_)
        rw [hfx]
    | add Y₁ Y₂ ih₁ ih₂ =>
      refine B.HtC_congr Dp (map_add _ _ _).symm (evalT_add _ _ _ _).symm ?_
      obtain ⟨v₁, r₁, n₁, c₁, hc₁, m₁⟩ := ih₁
      obtain ⟨v₂, r₂, n₂, c₂, hc₂, m₂⟩ := ih₂
      refine ⟨B.add1 v₁ v₂, ?_, ?_, c₁ * c₂, ?_, ?_⟩
      · refine (B.addFst_nat Dp.π v₁ v₂).trans ?_
        refine (B.addFst_hcongr (hker Y₁) (hker Y₂) hπσ r₁ r₂).trans ?_
        exact B.zeroFst_add (B.zero1 y)
      · have hS : N • (B.S1mk (B.add1 v₁ v₂)) = 0 := by
          have e : B.S1mk (B.add1 v₁ v₂) = B.S1mk v₁ + B.S1mk v₂ := rfl
          have z1 : N • B.S1mk v₁ = 0 := by
            rw [B.fibreFst_nsmul_mk]
            exact Sigma.ext (hNx Y₁) n₁
          have z2 : N • B.S1mk v₂ = 0 := by
            rw [B.fibreFst_nsmul_mk]
            exact Sigma.ext (hNx Y₂) n₂
          rw [e, nsmul_add, z1, z2, add_zero]
        rw [B.fibreFst_nsmul_mk] at hS
        exact (Sigma.ext_iff.mp hS).2
      · obtain ⟨a₁, ha₁⟩ := Ideal.mem_span_singleton'.mp (Dp.mem_span_of_π _ (hEmem Y₁))
        obtain ⟨a₂, ha₂⟩ := Ideal.mem_span_singleton'.mp (Dp.mem_span_of_π _ (hEmem Y₂))
        rw [Units.val_mul, hc₁, hc₂, ← ha₁, ← ha₂]
        linear_combination (a₁ * a₂) * Dp.η_sq
      · rw [B.nsmulSnd_addFst]
        refine (B.addFst_hcongr rfl rfl hNy m₁ m₂).trans ?_
        rw [B.addFst_smul, B.zeroSnd_addFst]
  obtain ⟨v, hvr, hv1, c, hc, hv2⟩ := claim Y
  obtain ⟨s1, s2⟩ := B.nsmul_of_same_red Dp hN (B.zero1 y) w₀ v hu hvr
  refine ⟨?_, c, hc, ?_⟩
  · rw [s1]
    exact hv1
  · rw [s2]
    exact hv2
end ReciprocityTheory.PGsh.BX
