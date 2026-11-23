-- Prove2me | solution 1 for StableMSR.Recovery.SingleWindows.singleton_board_describes_regional_incidences
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-23T00:12:22.193357+00:00
-- url     : https://prove2.me/submissions/a55a1486-1f04-40af-9b7f-0412b5245c64

import Definitions.Def_StableMSR_SingleWindowGrammar
import Theorems.Thm_StableMSR_Recovery_SingleWindows_singleton_grammar_exact_window_partitions
import Theorems.Thm_StableMSR_Recovery_WindowCSP_pairwise_windows_glue
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 12000
open StableMSR.Recovery StableMSR.Recovery.Havens StableMSR.Recovery.PartialDecompositions
open StableMSR.Recovery.DecompositionSearch StableMSR.Recovery.WindowCuts StableMSR.Recovery.SingleSearch
open RobertsonSeymour1986.GM5
open StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries StableMSR.Recovery.Supplement
open StableMSR.Recovery.WindowCSP StableMSR.Recovery.WindowPorts StableMSR.Recovery.WindowMasks StableMSR.Recovery.SingleWindows
open StableMSR.Recovery.WindowProfiles (piece keys)
theorem solution (x y : World) (e : ℚ) (dm : IsMetricArray x.dist) (h : Implements x e y) : WindowMasks.Describes x e y := by
  classical
  refine ⟨h.space,h.scenes,?_⟩
  intro u hu i hi;obtain ⟨I,P,unused,dry,live⟩:=h.roots u hu i hi
  refine ⟨I,P,?_,?_,?_⟩
  · intro L tr;by_cases key : i∈keys x u
    · by_cases pos : 0< scale x u
      · obtain ⟨nd,gen⟩:=(live key pos).1 L tr
        obtain ⟨_,A,validA,eq⟩:=(singleton_grammar_exact_window_partitions _ _ _ _ _ _).mp gen
        have fs:=(pairwise_windows_glue _ _ _ _ A dm pos.le validA).1
        rw [eq] at fs
        refine ⟨?_,fs.2.2.2⟩
        change List.Pairwise (·≠·) L at nd
        rw [List.pairwise_iff_getElem] at nd ⊢
        intro a b ha hb ab
        have ma : L[a]∈L.toFinset:=List.mem_toFinset.mpr (List.getElem_mem ..)
        have mb : L[b]∈L.toFinset:=List.mem_toFinset.mpr (List.getElem_mem ..)
        exact fs.2.2.1 ma mb (nd a b ha hb ab)
      · exact (dry key (le_of_not_gt pos) L tr).elim
    · have eq:=(unused key L).mp tr;subst L
      have emp : piece x u i=∅:=by
        apply Finset.eq_empty_iff_forall_notMem.mpr;intro v hv
        exact key (Finset.mem_image.mpr ⟨v,Finset.mem_univ _,(Finset.mem_filter.mp hv).2⟩)
      simp [WindowMasks.support,emp]
  · intro notKey;exact (unused notKey []).mpr rfl
  · intro key pos tw A ok _
    exact (live key pos).2 _ ((singleton_grammar_exact_window_partitions _ _ _ _ _ _).mpr ⟨tw,A,ok,rfl⟩)
