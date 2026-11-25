-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZRows_proof_36ca6318394a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:20:39.166914+00:00
-- url     : https://prove2.me/submissions/a91509a8-ab2c-4b2c-bf1e-608bbf75c472

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_VeryAmpleZRowsSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_CechPartitionSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_ZChartSmulSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_ZChartLocalSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PVeryAmpleZRows
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZRows_const_zero_e15e840f64ff

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
open VeryAmpleZRows
namespace GroundTheory.Heights₂.Heights.Kleiman
namespace VeryAmpleZRows
theorem _root_.solution (hPart : CechPartition.Statement.{u, v, w}) (hSmul : ZChartSmul.Statement.{u, v, w})
    (hLoc : ZChartLocal.Statement.{u, v, w}) : VeryAmpleZRows.Statement.{u, v, w} := by
  intro S _ Ω _ _ N x E _ _ _ _ G H r h hH J
  have hmono : ∀ I I' : Chart x, I.1 ⊆ I'.1 →
      secsOnZChart G.toSubSystem H.toSubSystem h I J ≤ secsOnZChart G.toSubSystem H.toSubSystem h I' J := by
    intro I I' hII'
    refine Submodule.span_mono ?_
    rintro e ⟨m, hm⟩
    exact ⟨m, (G.toSubSystem.twist (H.toSubSystem.pow (J.1.card * m))).mono I I' hII' _ hm⟩

  obtain ⟨j, hjJ⟩ := J.2.1
  obtain ⟨n, a, b, K, ha, hb, hab, hK⟩ := hH.affine j ((mem_support h).mp (J.2.2 hjJ))
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp at hab
    · exact hn

  let pt : ∀ i, i ∈ support x → Cech.Idx (support x) 0 := fun i hi =>
    ⟨⟨{i}, Finset.singleton_nonempty _, Finset.singleton_subset_iff.mpr hi⟩, Finset.card_singleton _⟩
  obtain ⟨i₀, hi₀⟩ := (K ⟨0, hn⟩).2.1
  have hi₀x : i₀ ∈ support x := (K ⟨0, hn⟩).2.2 hi₀
  refine ⟨hmono, fun I => iInf_le _ I, fun z _ hz => hz (pt i₀ hi₀x), ?_, ?_⟩
  ·
    intro s hs hds
    refine ⟨s (pt i₀ hi₀x), Submodule.mem_iInf _ |>.mpr fun I => ?_, fun I => const_zero hds I _⟩
    obtain ⟨i, hi⟩ := I.2.1
    rw [const_zero hds (pt i₀ hi₀x) (pt i (I.2.2 hi))]
    exact hmono (pt i (I.2.2 hi)).1 I (Finset.singleton_subset_iff.mpr hi)
      ((Submodule.mem_pi.mp hs) _ (Set.mem_univ _))
  ·
    intro p s hs hds
    have hjk : ∀ k, (K k).2.1.choose ∈ (K k).1 := fun k => (K k).2.1.choose_spec
    exact hPart S Ω E (support x) (fun I => secsOnZChart G.toSubSystem H.toSubSystem h I J) n a b
      (fun k => (K k).2.1.choose) (fun k => (K k).2.2 (hjk k)) hab
      (fun k I z hz => hSmul S Ω N x E G.toSubSystem H.toSubSystem r h hH.mem_secs J j hjJ I (a k) (ha k) z hz)
      (fun k I z hz => hSmul S Ω N x E G.toSubSystem H.toSubSystem r h hH.mem_secs J j hjJ I (b k) (hb k) z hz)
      (fun k I I' hI z hz => hLoc S Ω N x E G H r h hH.mem_secs J j hjJ (b k) (hb k) (K k) (hK k) _ (hjk k)
        I I' hI z hz)
      p s hs hds
end VeryAmpleZRows
end GroundTheory.Heights₂.Heights.Kleiman
