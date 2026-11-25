-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.Tor.ros_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:26:21.858744+00:00
-- url     : https://prove2.me/submissions/27a7914b-25ea-4417-9ff4-74a57abbd2e4

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_RosatiAdj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gen_unique__84c95b4ccdb0
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_surj_snd
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_surj_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_prod_ros
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_DVR_prod_sum__19c72914c5cb
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsCub_face__8d4277abb339
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_mulGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_pullGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isCub_cubV
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_prod_cub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_corr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_cub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_pull


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
variable {S : Scheme.{0}} {A : Over S} [GrpObj A]
variable [IsCommMonObj A] {L : LB A.left}
variable {Lr : RigLB A} (c : CubicalStr A Lr)
namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor
theorem _root_.solution (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (f g : A ⟶ A) [IsMonHom f] [IsMonHom g]
    (u : LB.Gen (LB.LinComb Lr.L (rosatiφ A f g) rosatiε)) (hu : u.IsGen)
    (h₀ : LB.Gen.Corr Lr.L _ _ _ _ (LB.pullGen Lr.L _ _ u (zero2 A)) (LB.oneGen Lr.L)) {T : Over S} {z : T.left} {J}
    (hJ : Good Lr.L z J) (x x' y : T ⟶ A) :
    val₂ u z J (x * x') y * cubV c z J x x' (y ≫ g) =
        cubV c z J (x ≫ f) (x' ≫ f) y * (val₂ u z J x y * val₂ u z J x' y) ∧
      val₂ u z J y (x * x') * cubV c z J y (x ≫ g) (x' ≫ g) =
        cubV c z J (y ≫ f) x x' * (val₂ u z J y x * val₂ u z J y x') := by
  let p₀ := x3 A 0
  let p₁ := x3 A 1
  let p₂ := x3 A 2
  have mf : ∀ {T : Over S} (a b : T ⟶ A), (a * b) ≫ f = (a ≫ f) * (b ≫ f) := fun a b => MonObj.mul_comp a b f
  have mg : ∀ {T : Over S} (a b : T ⟶ A), (a * b) ≫ g = (a ≫ g) * (b ≫ g) := fun a b => MonObj.mul_comp a b g
  have vp : ∀ {T T' : Over S} (ρ : T' ⟶ T) {z : T'.left} {J}, Good Lr.L z J → ∀ a b : T ⟶ A,
      val (LB.pullGen Lr.L _ _ u (lift a b).left) ρ.left z J = val₂ u z J (ρ ≫ a) (ρ ≫ b) := fun ρ z J hJ a b => by
    rw [val_pull hJ, ← Over.comp_left, comp_lift]; rfl
  have v1 : ∀ {y : (𝟙_ (Over S)).left} {J}, Good Lr.L y J → val₂ u y J (1 : 𝟙_ (Over S) ⟶ A) 1 = 1 := fun {y J} hJ => by
    have e : lift (1 : 𝟙_ (Over S) ⟶ A) (1 : 𝟙_ (Over S) ⟶ A) = lift η[A] η[A] := by simp [Hom.one_def]
    have := val_corr hJ h₀ (𝟙 _)
    rw [val_pull hJ, Category.id_comp, val_one] at this
    rw [val₂, e]; exact this
  let e : 𝟙_ (Over S) ⟶ G3 A := lift 1 (lift 1 1)
  have e₀ : e ≫ p₀ = 1 := by simp [e, p₀, x3]
  have e₁ : e ≫ p₁ = 1 := by simp [e, p₁, x3]
  have e₂ : e ≫ p₂ = 1 := by simp [e, p₂, x3]
  have sj : Function.Surjective ((snd A (A ⊗ A)).left ≫ (snd A A).left ≫ A.hom).appTop.hom :=
    surj_comp (surj_snd hG hA _) (surj_comp (surj_snd hG hA _) (hG _ _ hA).2)
  have he : e.left ≫ (snd A (A ⊗ A)).left ≫ (snd A A).left ≫ A.hom = 𝟙 _ := by
    rw [Over.w, Over.w]; exact Over.w e
  let ρ : T ⟶ G3 A := lift x (lift x' y)
  have r₀ : ρ ≫ p₀ = x := by simp [ρ, p₀, x3]
  have r₁ : ρ ≫ p₁ = x' := by simp [ρ, p₁, x3]
  have r₂ : ρ ≫ p₂ = y := by simp [ρ, p₂, x3]
  have gen : ∀ (a b a₁ b₁ a₂ b₂ k₁ k₂ k₃ l₁ l₂ l₃ : G3 A ⟶ A),
      (∀ (V : Type) [CommGroup V] (k : (G3 A ⟶ A) → V),
        (k (l₁ * l₂ * l₃) * (k (l₁ * l₂))⁻¹ * (k (l₁ * l₃))⁻¹ * (k (l₂ * l₃))⁻¹ * k l₁ * k l₂ * k l₃ * (k 1)⁻¹) *
          ((k ((a₁ ≫ f) * b₁) * (k (a₁ ≫ f))⁻¹ * (k b₁)⁻¹ * (k (a₁ * (b₁ ≫ g)))⁻¹ * k a₁ * k (b₁ ≫ g)) *
            (k ((a₂ ≫ f) * b₂) * (k (a₂ ≫ f))⁻¹ * (k b₂)⁻¹ * (k (a₂ * (b₂ ≫ g)))⁻¹ * k a₂ * k (b₂ ≫ g))) =
        (k ((a ≫ f) * b) * (k (a ≫ f))⁻¹ * (k b)⁻¹ * (k (a * (b ≫ g)))⁻¹ * k a * k (b ≫ g)) *
          (k (k₁ * k₂ * k₃) * (k (k₁ * k₂))⁻¹ * (k (k₁ * k₃))⁻¹ * (k (k₂ * k₃))⁻¹ * k k₁ * k k₂ * k k₃ * (k 1)⁻¹)) →
      e ≫ a = 1 → e ≫ b = 1 → e ≫ a₁ = 1 → e ≫ b₁ = 1 → e ≫ a₂ = 1 → e ≫ b₂ = 1 → e ≫ k₁ = 1 → e ≫ l₁ = 1 ∨ e ≫ l₂ = 1 →
      val₂ u z J (ρ ≫ a) (ρ ≫ b) * cubV c z J (ρ ≫ k₁) (ρ ≫ k₂) (ρ ≫ k₃) =
        cubV c z J (ρ ≫ l₁) (ρ ≫ l₂) (ρ ≫ l₃) * (val₂ u z J (ρ ≫ a₁) (ρ ≫ b₁) * val₂ u z J (ρ ≫ a₂) (ρ ≫ b₂)) := by
    intro a b a₁ b₁ a₂ b₂ k₁ k₂ k₃ l₁ l₂ l₃ hF ha hb ha₁ hb₁ ha₂ hb₂ hk hl
    have ev : ∀ {T' : Over S} (σ : T' ⟶ G3 A) {z : T'.left} {J}, Good Lr.L z J →
        val (LB.mulGen Lr.L _ _ _ _ (LB.pullGen Lr.L _ _ u (lift a b).left)
          (LB.pullGen Lr.L (thφ A (x3 A)) thε c.t (lift k₁ (lift k₂ k₃)).left)) σ.left z J =
          val₂ u z J (σ ≫ a) (σ ≫ b) * cubV c z J (σ ≫ k₁) (σ ≫ k₂) (σ ≫ k₃) ∧
        val (LB.mulGen Lr.L _ _ _ _ (LB.pullGen Lr.L (thφ A (x3 A)) thε c.t (lift l₁ (lift l₂ l₃)).left)
          (LB.mulGen Lr.L _ _ _ _ (LB.pullGen Lr.L _ _ u (lift a₁ b₁).left) (LB.pullGen Lr.L _ _ u (lift a₂ b₂).left)))
          σ.left z J = cubV c z J (σ ≫ l₁) (σ ≫ l₂) (σ ≫ l₃) *
            (val₂ u z J (σ ≫ a₁) (σ ≫ b₁) * val₂ u z J (σ ≫ a₂) (σ ≫ b₂)) := fun σ z J hJ =>
      ⟨(val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (vp σ hJ _ _) (val_cub c σ hJ _ _ _)),
        (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (val_cub c σ hJ _ _ _)
          ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (vp σ hJ _ _) (vp σ hJ _ _))))⟩
    refine (ev ρ hJ).1.symm.trans (Eq.trans (gen_unique' Lr.isLB (fun V _ k => ?_) _ e.left he sj
      (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hu _) (DVR.pullGen_isGen _ _ _ _ c.isGen _))
      (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ c.isGen _) (DVR.mulGen_isGen _ _ _ _ _ _ _
        (DVR.pullGen_isGen _ _ _ _ hu _) (DVR.pullGen_isGen _ _ _ _ hu _))) (fun y I hI => ?_) _ ρ.left z J hJ) (ev ρ hJ).2)
    · exact (DVR.prod_sum₂ (K := thK) (K' := Fin 6 ⊕ Fin 6) (U := V) _ (prod_cub l₁ l₂ l₃ k)
        (DVR.prod_sum₂ (K := Fin 6) (K' := Fin 6) (U := V) _ (prod_ros f g a₁ b₁ k) (prod_ros f g a₂ b₂ k))).trans
        ((hF V fun q => k q.left).trans (DVR.prod_sum₂ (K := Fin 6) (K' := thK) (U := V) _ (prod_ros f g a b k)
          (prod_cub k₁ k₂ k₃ k)).symm)
    · have C : IsCub (cubV c y I) := isCub_cubV c hI
      refine (ev e hI).1.trans (Eq.trans ?_ (ev e hI).2.symm)
      rw [ha, hb, ha₁, hb₁, ha₂, hb₂, hk, v1 hI, C.face]
      rcases hl with hl | hl
      · rw [hl, C.face]; simp
      · rw [hl, C.face₂]; simp
  have o₁ : e ≫ (p₀ * p₁) = 1 := (MonObj.comp_mul _ _ _).trans (by rw [e₀, e₁, _root_.mul_one])
  have s₁ : ρ ≫ (p₀ * p₁) = x * x' := (MonObj.comp_mul _ _ _).trans (by rw [r₀, r₁])
  constructor
  · have := gen (p₀ * p₁) p₂ p₀ p₂ p₁ p₂ p₀ p₁ (p₂ ≫ g) (p₀ ≫ f) (p₁ ≫ f) p₂ (fun V _ k => by
      rw [mf]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel) o₁ e₂ e₀ e₂ e₁ e₂ e₀ (Or.inl (by rw [← Category.assoc, e₀, MonObj.one_comp]))
    rwa [s₁, ← Category.assoc ρ p₂, ← Category.assoc ρ p₀, ← Category.assoc ρ p₁, r₀, r₁, r₂] at this
  · have := gen p₂ (p₀ * p₁) p₂ p₀ p₂ p₁ p₂ (p₀ ≫ g) (p₁ ≫ g) (p₂ ≫ f) p₀ p₁ (fun V _ k => by
      rw [mg, _root_.mul_assoc p₂, _root_.mul_assoc (p₂ ≫ f)]
      have : (p₀ * p₁) ≫ g = (p₀ ≫ g) * (p₁ ≫ g) := mg _ _
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel) e₂ o₁ e₂ e₀ e₂ e₁ e₂ (Or.inr e₀)
    rwa [s₁, ← Category.assoc ρ p₂, ← Category.assoc ρ p₀, ← Category.assoc ρ p₁, r₀, r₁, r₂] at this
end ReciprocityTheory.ChartRestriction.G.Geo.Tor
