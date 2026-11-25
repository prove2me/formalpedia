-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_CechDouble_dbl_good_11420f17daf7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:22:41.741972+00:00
-- url     : https://prove2.me/submissions/df420daf-8a66-40e1-a9cf-c0fb804ed523

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_CechDoubleSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PCechDSq
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PCechDoubleStair
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PCechDouble
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_CechDouble_dE_dE_f28a19d9aaf1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_CechDouble_vW_vW_ff5eda162f1c

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
noncomputable section
universe u v w
open GroundTheory.Heights₂.Heights.Kleiman.CechDouble
open Cech
variable {S : Type u} [CommRing S] {E : Type v} [AddCommGroup E] [Module S E] {Ω : Type w} [Field Ω] {N r : ℕ}
  {x : Fin (N + 1) → Ω} {y : Fin (r + 1) → Ω}
variable (M : Chart x → Chart y → Submodule S E)
variable {M}
variable (Ax : Chart x → Submodule S E) (Bx : Chart y → Submodule S E)
namespace GroundTheory.Heights₂.Heights.Kleiman.CechDouble
theorem _root_.solution (hM₁ : ∀ (I I' : Chart x) (J : Chart y), I.1 ⊆ I'.1 → M I J ≤ M I' J)
    (hM₂ : ∀ (I : Chart x) (J J' : Chart y), J.1 ⊆ J'.1 → M I J ≤ M I J')
    (hA : ∀ I, Cech.AugExact S (M I) (Ax I)) (hB : ∀ J, Cech.AugExact S (fun I => M I J) (Bx J)) :
    (dbl Ax Bx hM₁ hM₂ hA hB).Good where
  ha p := LinearMap.ext fun s => Subtype.ext (funext fun I' => funext fun J => by
    change dE S E (support x) p s.1 I' = vW S E x y p 0 (fun I _ => s.1 I) I' J
    rw [vW_apply])
  hc _ := LinearMap.ext fun _ => rfl
  ka p := LinearMap.ker_eq_bot'.mpr fun s hs => Subtype.ext (funext fun I =>
    (hA I.1).2.1 _ (s.2 I (Set.mem_univ _)) fun J => congrFun (congrFun (congrArg Subtype.val hs) I) J)
  ra p := by
    ext f
    rw [LinearMap.mem_ker, LinearMap.mem_range]
    constructor
    · intro hf
      have hI : ∀ I : Idx (support x) p, ∃ b ∈ Ax I.1, ∀ J, f.1 I J = b := fun I =>
        (hA I.1).2.2.1 (f.1 I) (fun J _ => (mem_Dsub M).1 f.2 I J) (congrFun (congrArg Subtype.val hf) I)
      choose b hb hbf using hI
      exact ⟨⟨b, fun I _ => hb I⟩, Subtype.ext (funext fun I => funext fun J => (hbf I J).symm)⟩
    · rintro ⟨s, rfl⟩
      exact Subtype.ext (funext fun I => dE_const (s.1 I))
  rh p q := by
    ext f
    rw [LinearMap.mem_ker, LinearMap.mem_range]
    constructor
    · intro hf
      have hI : ∀ I : Idx (support x) p, ∃ t ∈ Cdeg (fun _ : Chart y => E) (M I.1) q,
          dE S E (support y) q t = f.1 I := fun I =>
        (hA I.1).2.2.2 q (f.1 I) (fun J _ => (mem_Dsub M).1 f.2 I J) (congrFun (congrArg Subtype.val hf) I)
      choose t ht htf using hI
      exact ⟨⟨t, (mem_Dsub M).2 fun I J => ht I J (Set.mem_univ _)⟩, Subtype.ext (funext htf)⟩
    · rintro ⟨s, rfl⟩
      exact Subtype.ext (funext fun I => dE_dE q (s.1 I))
  kc q := LinearMap.ker_eq_bot'.mpr fun t ht => Subtype.ext (funext fun J =>
    (hB J.1).2.1 _ (t.2 J (Set.mem_univ _)) fun I => congrFun (congrFun (congrArg Subtype.val ht) I) J)
  rc q := by
    ext f
    rw [LinearMap.mem_ker, LinearMap.mem_range]
    constructor
    · intro hf
      have hJ : ∀ J : Idx (support y) q, ∃ b ∈ Bx J.1, ∀ I, f.1 I J = b := fun J =>
        (hB J.1).2.2.1 (fun I => f.1 I J) (fun I _ => (mem_Dsub M).1 f.2 I J) (funext fun I' => by
          rw [← vW_apply]
          exact congrFun (congrFun (congrArg Subtype.val hf) I') J)
      choose b hb hbf using hJ
      exact ⟨⟨b, fun J _ => hb J⟩, Subtype.ext (funext fun I => funext fun J => (hbf J I).symm)⟩
    · rintro ⟨t, rfl⟩
      refine Subtype.ext (funext fun I' => funext fun J => ?_)
      change vW S E x y 0 q _ I' J = 0
      rw [vW_apply]
      exact congrFun (dE_const (t.1 J)) I'
  rv p q := by
    ext f
    rw [LinearMap.mem_ker, LinearMap.mem_range]
    constructor
    · intro hf
      have hJ : ∀ J : Idx (support y) q, ∃ t ∈ Cdeg (fun _ : Chart x => E) (fun I => M I J.1) p,
          dE S E (support x) p t = fun I => f.1 I J := fun J =>
        (hB J.1).2.2.2 p (fun I => f.1 I J) (fun I _ => (mem_Dsub M).1 f.2 I J) (funext fun I' => by
          rw [← vW_apply]
          exact congrFun (congrFun (congrArg Subtype.val hf) I') J)
      choose t ht htf using hJ
      refine ⟨⟨fun I J => t J I, (mem_Dsub M).2 fun I J => ht J I (Set.mem_univ _)⟩,
        Subtype.ext (funext fun I' => funext fun J => ?_)⟩
      change vW S E x y p q _ I' J = _
      rw [vW_apply]
      exact congrFun (htf J) I'
    · rintro ⟨s, rfl⟩
      exact Subtype.ext (vW_vW p q s.1)
end GroundTheory.Heights₂.Heights.Kleiman.CechDouble
