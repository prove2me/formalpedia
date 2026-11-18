-- Prove2me | solution 1 for RandomOracleUnitarySynthesis.synthesis_entropy_resampling
-- status  : ACCEPTED   (prove)
-- author  : @I am wealthy
-- created : 2026-11-17T19:08:14.940027+00:00
-- url     : https://prove2.me/submissions/a1b019ba-701b-4c8a-b753-72d5c181074c

import Mathlib
import Definitions.Def_RandomOracleUnitarySynthesis_synthesis_resampling
import Definitions.Def_RandomOracleUnitarySynthesis_synthesis_circuit


/- Module RandomOracleProjectionEnergy -/

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace RandomOracleUnitarySynthesis.ResamplingProof
open Finset
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma projection_orthogonal (P : E→E)
    (hsym:∀x y,inner ℝ (P x) y=inner ℝ x (P y)) (hid:∀x,P (P x)=P x) (x y : E) :
    inner ℝ (P x) (y-P y)=0 := by
  rw [inner_sub_right,hsym,hsym,hid,sub_self]

lemma projection_loss (P : E→E)
    (hsym:∀x y,inner ℝ (P x) y=inner ℝ x (P y)) (hid:∀x,P (P x)=P x) (x : E) :
    ‖x-P x‖^2=‖x‖^2-‖P x‖^2 := by
  have hh:=hsym x (P x)
  rw [hid,real_inner_self_eq_norm_sq] at hh
  rw [norm_sub_sq_real]
  linarith

def projectionPath (P : ℕ→E→E) (a : E) : ℕ→E
  | 0=>a
  | i+1=>P i (projectionPath P a i)

lemma projectionPath_telescope (P : ℕ→E→E) (a : E) (T : ℕ) :
    (∑i∈range T,(projectionPath P a i-projectionPath P a (i+1)))=a-projectionPath P a T := by
  induction T with
  | zero => simp [projectionPath]
  | succ T ih => rw [sum_range_succ,ih];abel

lemma real_sum_telescope (D : ℕ→ℝ) (T : ℕ) :
    (∑i∈range T,(D i-D (i+1)))=D 0-D T := by
  induction T with
  | zero=>simp
  | succ T ih=>rw [sum_range_succ,ih];ring

/-- Finite noncommuting orthogonal-projection energy inequality. This is
the Hilbert-space core of the reversible resampling estimate; concrete
resampling-to-operator identities are established separately. -/
theorem projection_product_energy (P : ℕ→E→E) (a : E) (T : ℕ)
    (hsym:∀i<T,∀x y,inner ℝ (P i x) y=inner ℝ x (P i y))
    (hid:∀i<T,∀x,P i (P i x)=P i x) :
    inner ℝ a (a-projectionPath P a T)  ≤  2*(∑i∈range T,‖a-P i a‖^2) := by
  let v:=projectionPath P a
  let S:=∑i∈range T,‖a-P i a‖^2
  let Q:=∑i∈range T,‖v i-P i (v i)‖^2
  let D:=inner ℝ a (a-v T)
  have hS:0 ≤ S := sum_nonneg (fun i _=>sq_nonneg _)
  have hQ:0 ≤ Q := sum_nonneg (fun i _=>sq_nonneg _)
  have hsum:D=∑i∈range T,inner ℝ (a-P i a) (v i-P i (v i)) := by
    dsimp only [D]
    rw [← projectionPath_telescope P a T,inner_sum]
    apply sum_congr rfl
    intro i hi
    have horth:=projection_orthogonal (P i) (hsym i (mem_range.mp hi)) (hid i (mem_range.mp hi)) a (v i)
    rw [inner_sub_left,horth,sub_zero]
    rfl
  have hbound:D ≤ Real.sqrt S*Real.sqrt Q := by
    rw [hsum]
    have hc:=Real.sum_mul_le_sqrt_mul_sqrt (range T) (fun i=>‖a-P i a‖) (fun i=>‖v i-P i (v i)‖)
    exact (sum_le_sum (fun i _=>real_inner_le_norm _ _)).trans hc
  have hQloss:Q=‖a‖^2-‖v T‖^2 := by
    have he:Q=∑i∈range T,(‖v i‖^2-‖v (i+1)‖^2) := by
      apply sum_congr rfl
      intro i hi
      exact projection_loss (P i) (hsym i (mem_range.mp hi)) (hid i (mem_range.mp hi)) (v i)
    rw [he,real_sum_telescope]
    rfl
  have hDQ:Q ≤ 2*D := by
    rw [hQloss]
    dsimp only [D]
    rw [inner_sub_right,real_inner_self_eq_norm_sq]
    nlinarith [sq_nonneg ‖a-v T‖,norm_sub_sq_real a (v T)]
  have hD:0 ≤ D := by linarith
  have hsquare:=pow_le_pow_left₀ hD hbound 2
  rw [mul_pow,Real.sq_sqrt hS,Real.sq_sqrt hQ] at hsquare
  have hm:=mul_le_mul_of_nonneg_left hDQ hS
  change D ≤ 2*S
  by_cases hd:D=0
  · rw [hd];positivity
  · have hpos:0<D := lt_of_le_of_ne hD (Ne.symm hd)
    nlinarith

end RandomOracleUnitarySynthesis.ResamplingProof

/- Module RandomOracleResamplingBasics -/

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace RandomOracleUnitarySynthesis.ResamplingProof
open Matrix Finset Classical
open scoped ComplexConjugate
variable {n m m₀ k : ℕ}

lemma allowed_update (C : synthesis_Circuit n m m₀ k) (r : ℝ) (f : synthesis_Oracle m₀)
    (x : synthesis_Bits m₀) (b : Bool) :
    synthesis_resampleAllowed C r (Function.update f x b) x ↔ synthesis_resampleAllowed C r f x := by
  simp only [synthesis_resampleAllowed,Function.update_idem]

lemma flip_involutive (x : synthesis_Bits m₀) : Function.Involutive (fun f:synthesis_Oracle m₀=>synthesis_flip f x) := by
  intro f
  funext y
  by_cases h:y=x <;> simp [synthesis_flip,h]

lemma allowed_flip (C : synthesis_Circuit n m m₀ k) (r : ℝ) (f : synthesis_Oracle m₀)
    (x : synthesis_Bits m₀) :
    synthesis_resampleAllowed C r (synthesis_flip f x) x ↔ synthesis_resampleAllowed C r f x :=
  allowed_update C r f x (!f x)

def step (C : synthesis_Circuit n m m₀ k) (r : ℝ) (x : synthesis_Bits m₀)
    (f : synthesis_Oracle m₀) (b : Bool) : synthesis_Oracle m₀ :=
  if synthesis_resampleAllowed C r f x then Function.update f x b else f

/-- Store the spent initial bit in its seed position. The map is an exact
involution on a pair of complete truth tables. It is the concrete
reversibility underlying the resampling proof. -/
def swapStep (C : synthesis_Circuit n m m₀ k) (r : ℝ) (x : synthesis_Bits m₀)
    (z : synthesis_Oracle m₀×synthesis_Oracle m₀) : synthesis_Oracle m₀×synthesis_Oracle m₀ :=
  if synthesis_resampleAllowed C r z.1 x then
    (Function.update z.1 x (z.2 x),Function.update z.2 x (z.1 x)) else z

lemma swapStep_involutive (C : synthesis_Circuit n m m₀ k) (r : ℝ) (x : synthesis_Bits m₀) :
    Function.Involutive (swapStep C r x) := by
  intro z
  rcases z with ⟨f,c⟩
  by_cases ha:synthesis_resampleAllowed C r f x
  · have ha':synthesis_resampleAllowed C r (Function.update f x (c x)) x := (allowed_update C r f x _).mpr ha
    simp [swapStep,ha,ha',Function.update_idem]
  · simp [swapStep,ha]

def swapEquiv (C : synthesis_Circuit n m m₀ k) (r : ℝ) (x : synthesis_Bits m₀) :
    (synthesis_Oracle m₀×synthesis_Oracle m₀) ≃ (synthesis_Oracle m₀×synthesis_Oracle m₀) :=
  (swapStep_involutive C r x).toPerm

lemma swapStep_fst (C : synthesis_Circuit n m m₀ k) (r : ℝ) (x : synthesis_Bits m₀)
    (z : synthesis_Oracle m₀×synthesis_Oracle m₀) :
    (swapStep C r x z).1=step C r x z.1 (z.2 x) := by
  unfold swapStep step
  split_ifs <;> rfl

lemma swapStep_future (C : synthesis_Circuit n m m₀ k) (r : ℝ) (x y : synthesis_Bits m₀)
    (hxy:y≠x) (z : synthesis_Oracle m₀×synthesis_Oracle m₀) :
    (swapStep C r x z).2 y=z.2 y := by
  unfold swapStep
  split_ifs <;> simp [hxy]

def swapPath (C : synthesis_Circuit n m m₀ k) (r : ℝ) :
    ℕ→(synthesis_Oracle m₀×synthesis_Oracle m₀)→(synthesis_Oracle m₀×synthesis_Oracle m₀)
  | 0,z=>z
  | i+1,z=>if hi:i<Fintype.card (synthesis_Bits m₀) then
      swapStep C r (synthesis_order m₀ ⟨i,hi⟩) (swapPath C r i z) else swapPath C r i z

lemma swapPath_bijective (C : synthesis_Circuit n m m₀ k) (r : ℝ) (i : ℕ) :
    Function.Bijective (swapPath C r i) := by
  induction i with
  | zero => exact Function.bijective_id
  | succ i ih =>
    by_cases hi:i<Fintype.card (synthesis_Bits m₀)
    · simp only [swapPath,dif_pos hi]
      exact (swapStep_involutive C r (synthesis_order m₀ ⟨i,hi⟩)).bijective.comp ih
    · simpa only [swapPath,dif_neg hi] using ih

lemma swapPath_fresh (C : synthesis_Circuit n m m₀ k) (r : ℝ)
    (f coins : synthesis_Oracle m₀) (i : ℕ) (j : Fin (Fintype.card (synthesis_Bits m₀)))
    (hij:i ≤ j.val) : (swapPath C r i (f,coins)).2 (synthesis_order m₀ j)=coins (synthesis_order m₀ j) := by
  induction i with
  | zero => rfl
  | succ i ih =>
    have hi:i<Fintype.card (synthesis_Bits m₀) := by omega
    rw [swapPath,dif_pos hi,swapStep_future]
    · exact ih (by omega)
    · intro hh
      have he:= (synthesis_order m₀).injective hh
      have hv:j.val=i := congrArg Fin.val he
      omega

/-- The reversible path has exactly the same current function as the
published procedure using fresh independent bits. The selected set is
retained by the public procedure, and is not replaced or weakened. -/
lemma swapPath_current (C : synthesis_Circuit n m m₀ k) (r : ℝ)
    (f coins : synthesis_Oracle m₀) (i : ℕ) :
    (swapPath C r i (f,coins)).1=(synthesis_resamplePath C r f coins i).1 := by
  induction i with
  | zero => rfl
  | succ i ih =>
    by_cases hi:i<Fintype.card (synthesis_Bits m₀)
    · rw [swapPath,dif_pos hi,swapStep_fst]
      rw [swapPath_fresh C r f coins i ⟨i,hi⟩ (le_refl _),ih]
      simp only [synthesis_resamplePath,dif_pos hi,step]
      split_ifs <;> rfl
    · simpa only [swapPath,dif_neg hi,synthesis_resamplePath] using ih

end RandomOracleUnitarySynthesis.ResamplingProof

/- Module RandomOracleResamplingStationarity -/

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace RandomOracleUnitarySynthesis.ResamplingProof
open Matrix Finset Classical
open scoped ComplexConjugate
variable {n m m₀ k : ℕ}

lemma average_const {α : Type} [Fintype α] [Nonempty α] (c : ℝ) :
    synthesis_average (fun _:α=>c)=c := by
  have hc:(Fintype.card α:ℝ)≠0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [synthesis_average,sum_const,card_univ,nsmul_eq_mul]
  exact mul_div_cancel_left₀ c hc

lemma average_add {α : Type} [Fintype α] (f g : α→ℝ) :
    synthesis_average (fun a=>f a+g a)=synthesis_average f+synthesis_average g := by
  simp only [synthesis_average,sum_add_distrib,add_div]

lemma average_comp {α : Type} [Fintype α] (e : α≃α) (f : α→ℝ) :
    synthesis_average (fun a=>f (e a))=synthesis_average f := by
  unfold synthesis_average
  rw [e.sum_comp]

lemma average_bit (x : synthesis_Bits m₀) (F : Bool→ℝ) :
    synthesis_average (fun coins:synthesis_Oracle m₀=>F (coins x))=(F false+F true)/2 := by
  let e:Equiv.Perm (synthesis_Oracle m₀):=(flip_involutive x).toPerm
  have hs:∀coins:synthesis_Oracle m₀,F (coins x)+F ((e coins) x)=F false+F true := by
    intro coins
    change F (coins x)+F ((synthesis_flip coins x) x)=_
    simp only [synthesis_flip,Function.update_self]
    cases coins x <;> simp [add_comm]
  have hh:=average_add (fun coins:synthesis_Oracle m₀=>F (coins x)) (fun coins=>F ((e coins) x))
  rw [average_comp e (fun coins:synthesis_Oracle m₀=>F (coins x))] at hh
  have he:synthesis_average (fun coins:synthesis_Oracle m₀=>F (coins x)+F ((e coins) x))=F false+F true := by
    simp only [hs,average_const]
  rw [he] at hh
  linarith

lemma sum_swapPath {α : Type} [AddCommMonoid α] (C : synthesis_Circuit n m m₀ k) (r : ℝ)
    (i : ℕ) (h : synthesis_Oracle m₀×synthesis_Oracle m₀→α) :
    (∑f,∑coins,h (swapPath C r i (f,coins)))=(∑f,∑coins,h (f,coins)) := by
  simpa only [Fintype.sum_prod_type,Equiv.ofBijective_apply] using
    (Equiv.ofBijective (swapPath C r i) (swapPath_bijective C r i)).sum_comp h

lemma double_average_swapPath (C : synthesis_Circuit n m m₀ k) (r : ℝ)
    (i : ℕ) (h : synthesis_Oracle m₀×synthesis_Oracle m₀→ℝ) :
    synthesis_average (fun f=>synthesis_average (fun coins=>h (swapPath C r i (f,coins))))=
      synthesis_average (fun f=>synthesis_average (fun coins=>h (f,coins))) := by
  unfold synthesis_average
  rw [← sum_div,← sum_div,sum_swapPath]

/-- Uniform truth-table marginal preservation for every actual intermediate
function, derived from the concrete reversible state-and-spent-seed map. -/
theorem average_path_current (C : synthesis_Circuit n m m₀ k) (r : ℝ) (i : ℕ)
    (h : synthesis_Oracle m₀→ℝ) :
    synthesis_average (fun f=>synthesis_average (fun coins=>h (synthesis_resamplePath C r f coins i).1))=
      synthesis_average h := by
  have hs:∀f coins,h (synthesis_resamplePath C r f coins i).1=h (swapPath C r i (f,coins)).1 :=
    fun f coins=>congrArg h (swapPath_current C r f coins i).symm
  simp_rw [hs]
  rw [double_average_swapPath C r i (fun z=>h z.1)]
  simp only [average_const]

end RandomOracleUnitarySynthesis.ResamplingProof

/- Module RandomOracleResamplingFresh -/

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace RandomOracleUnitarySynthesis.ResamplingProof
open Matrix Finset Classical
open scoped ComplexConjugate
variable {n m m₀ k : ℕ}

lemma average_div {α : Type} [Fintype α] (f : α→ℝ) (d : ℝ) :
    synthesis_average (fun a=>f a/d)=synthesis_average f/d := by
  unfold synthesis_average
  rw [← sum_div]
  ring

/-- Every unvisited fair bit is independent of the complete actual path
prefix, including its selected-coordinate set. -/
lemma path_coins_update (C : synthesis_Circuit n m m₀ k) (r : ℝ)
    (f coins : synthesis_Oracle m₀) (i : ℕ) (j : Fin (Fintype.card (synthesis_Bits m₀)))
    (hij:i ≤ j.val) (b : Bool) :
    synthesis_resamplePath C r f (Function.update coins (synthesis_order m₀ j) b) i=
      synthesis_resamplePath C r f coins i := by
  induction i with
  | zero=>rfl
  | succ i ih=>
    have hi:i<Fintype.card (synthesis_Bits m₀) := by omega
    have hne:synthesis_order m₀ ⟨i,hi⟩≠synthesis_order m₀ j := by
      intro hh
      have hv:i=j.val := congrArg Fin.val ((synthesis_order m₀).injective hh)
      omega
    simp only [synthesis_resamplePath,dif_pos hi,ih (by omega),Function.update_of_ne hne]

lemma path_coins_flip (C : synthesis_Circuit n m m₀ k) (r : ℝ)
    (f coins : synthesis_Oracle m₀) (i : ℕ) (j : Fin (Fintype.card (synthesis_Bits m₀)))
    (hij:i ≤ j.val) :
    synthesis_resamplePath C r f (synthesis_flip coins (synthesis_order m₀ j)) i=
      synthesis_resamplePath C r f coins i := path_coins_update C r f coins i j hij _

lemma average_fresh_bit (C : synthesis_Circuit n m m₀ k) (r : ℝ)
    (f : synthesis_Oracle m₀) (i : ℕ) (hi:i<Fintype.card (synthesis_Bits m₀))
    (H : (synthesis_Oracle m₀×Finset (synthesis_Bits m₀))→Bool→ℝ) :
    synthesis_average (fun coins:synthesis_Oracle m₀=>
      H (synthesis_resamplePath C r f coins i) (coins (synthesis_order m₀ ⟨i,hi⟩)))=
    synthesis_average (fun coins:synthesis_Oracle m₀=>
      (H (synthesis_resamplePath C r f coins i) false+H (synthesis_resamplePath C r f coins i) true)/2) := by
  let x:=synthesis_order m₀ ⟨i,hi⟩
  let F:=fun coins:synthesis_Oracle m₀=>H (synthesis_resamplePath C r f coins i) (coins x)
  let G:=fun coins:synthesis_Oracle m₀=>
    H (synthesis_resamplePath C r f coins i) false+H (synthesis_resamplePath C r f coins i) true
  let e:Equiv.Perm (synthesis_Oracle m₀):=(flip_involutive x).toPerm
  have he:synthesis_average (fun coins=>F (e coins))=synthesis_average F := average_comp e F
  have hs:∀coins:synthesis_Oracle m₀,F coins+F (e coins)=G coins := by
    intro coins
    dsimp only [F,G]
    change H (synthesis_resamplePath C r f coins i) (coins x)+
      H (synthesis_resamplePath C r f (synthesis_flip coins x) i) ((synthesis_flip coins x) x)=_
    rw [path_coins_flip C r f coins i ⟨i,hi⟩ (le_refl _)]
    simp only [synthesis_flip,Function.update_self]
    cases coins x <;> simp [add_comm]
  have hh:=average_add F (fun coins=>F (e coins))
  rw [he] at hh
  have hG:synthesis_average (fun coins=>F coins+F (e coins))=synthesis_average G := by simp only [hs]
  rw [hG] at hh
  change synthesis_average F=synthesis_average (fun coins=>G coins/2)
  rw [average_div]
  linarith

/-- Scalar conditional averaging for the genuine finite path. -/
def oneStepOp (C : synthesis_Circuit n m m₀ k) (r : ℝ) (x : synthesis_Bits m₀)
    (h : synthesis_Oracle m₀→ℝ) (f : synthesis_Oracle m₀) : ℝ :=
  (h (step C r x f false)+h (step C r x f true))/2

lemma average_next (C : synthesis_Circuit n m m₀ k) (r : ℝ)
    (f : synthesis_Oracle m₀) (i : ℕ) (hi:i<Fintype.card (synthesis_Bits m₀))
    (h : synthesis_Oracle m₀→ℝ) :
    synthesis_average (fun coins:synthesis_Oracle m₀=>h (synthesis_resamplePath C r f coins (i+1)).1)=
      synthesis_average (fun coins:synthesis_Oracle m₀=>
        oneStepOp C r (synthesis_order m₀ ⟨i,hi⟩) h (synthesis_resamplePath C r f coins i).1) := by
  have hp:∀coins:synthesis_Oracle m₀,(synthesis_resamplePath C r f coins (i+1)).1=
      step C r (synthesis_order m₀ ⟨i,hi⟩) (synthesis_resamplePath C r f coins i).1
        (coins (synthesis_order m₀ ⟨i,hi⟩)) := by
    intro coins
    simp only [synthesis_resamplePath,dif_pos hi,step]
    split_ifs <;> rfl
  simp_rw [hp]
  exact average_fresh_bit C r f i hi (fun prev b=>h (step C r (synthesis_order m₀ ⟨i,hi⟩) prev.1 b))

end RandomOracleUnitarySynthesis.ResamplingProof

/- Module RandomOracleFiniteProjections -/

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace RandomOracleUnitarySynthesis.ResamplingProof
open Matrix Finset Classical
variable {ι : Type} [Fintype ι]

def permutationAction (e : Equiv.Perm ι) : EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e.symm

lemma permutationAction_apply (e : Equiv.Perm ι) (v : EuclideanSpace ℝ ι) (i : ι) :
    permutationAction e v i=v (e i) := rfl

lemma permutationAction_involutive (e : Equiv.Perm ι) (he:Function.Involutive e) :
    Function.Involutive (permutationAction e) := by
  intro v
  apply PiLp.ext
  intro i
  change v (e (e i))=v i
  rw [he i]

def pairProjection (e : Equiv.Perm ι) (v : EuclideanSpace ℝ ι) : EuclideanSpace ℝ ι :=
  (1/2:ℝ) • (v+permutationAction e v)

lemma pairProjection_apply (e : Equiv.Perm ι) (v : EuclideanSpace ℝ ι) (i : ι) :
    pairProjection e v i=(v i+v (e i))/2 := by
  change (1/2:ℝ)*(v i+permutationAction e v i)=_
  rw [permutationAction_apply]
  ring

lemma pairProjection_idempotent (e : Equiv.Perm ι) (he:Function.Involutive e) (v : EuclideanSpace ℝ ι) :
    pairProjection e (pairProjection e v)=pairProjection e v := by
  apply PiLp.ext
  intro i
  simp only [pairProjection_apply,he i]
  ring

lemma pairProjection_symmetric (e : Equiv.Perm ι) (he:Function.Involutive e) (u v : EuclideanSpace ℝ ι) :
    inner ℝ (pairProjection e u) v=inner ℝ u (pairProjection e v) := by
  have hh:inner ℝ (permutationAction e u) v=inner ℝ u (permutationAction e v) := by
    have ht:=(permutationAction e).inner_map_map u (permutationAction e v)
    rwa [permutationAction_involutive e he v] at ht
  simp only [pairProjection,inner_smul_left,inner_smul_right,inner_add_left,inner_add_right,
    conj_trivial]
  rw [hh]

variable {n m m₀ k : ℕ}

def lazyFlip (C : synthesis_Circuit n m m₀ k) (r : ℝ) (x : synthesis_Bits m₀)
    (f : synthesis_Oracle m₀) : synthesis_Oracle m₀ :=
  if synthesis_resampleAllowed C r f x then synthesis_flip f x else f

lemma lazyFlip_involutive (C : synthesis_Circuit n m m₀ k) (r : ℝ) (x : synthesis_Bits m₀) :
    Function.Involutive (lazyFlip C r x) := by
  intro f
  by_cases ha:synthesis_resampleAllowed C r f x
  · have hb:= (allowed_flip C r f x).mpr ha
    simp [lazyFlip,ha,hb,flip_involutive x f]
  · simp [lazyFlip,ha]

def lazyFlipEquiv (C : synthesis_Circuit n m m₀ k) (r : ℝ) (x : synthesis_Bits m₀) :
    Equiv.Perm (synthesis_Oracle m₀) := (lazyFlip_involutive C r x).toPerm

lemma forced_pair_sum (C : synthesis_Circuit n m m₀ k) (r : ℝ) (x : synthesis_Bits m₀)
    (h : synthesis_Oracle m₀→ℝ) (f : synthesis_Oracle m₀) :
    oneStepOp C r x h f=(h f+h (lazyFlip C r x f))/2 := by
  by_cases ha:synthesis_resampleAllowed C r f x
  · simp only [oneStepOp,step,if_pos ha,lazyFlip]
    have hf:Function.update f x (f x)=f := Function.update_eq_self x f
    cases hfx:f x
    · have h0:Function.update f x false=f := by simpa only [hfx] using hf
      simp only [synthesis_flip,hfx,Bool.not_false,h0]
    · have h1:Function.update f x true=f := by simpa only [hfx] using hf
      simp only [synthesis_flip,hfx,Bool.not_true,h1]
      ring
  · simp only [oneStepOp,step,lazyFlip,if_neg ha]

/-- Scalar form of the exact L2 projection at a resampling coordinate. -/
lemma oneStepOp_projection (C : synthesis_Circuit n m m₀ k) (r : ℝ) (x : synthesis_Bits m₀)
    (v : EuclideanSpace ℝ (synthesis_Oracle m₀)) (f : synthesis_Oracle m₀) :
    pairProjection (lazyFlipEquiv C r x) v f=oneStepOp C r x v f := by
  rw [pairProjection_apply,forced_pair_sum]
  rfl

end RandomOracleUnitarySynthesis.ResamplingProof

/- Module RandomOracleResamplingDP -/

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace RandomOracleUnitarySynthesis.ResamplingProof
open Matrix Finset Classical

lemma average_sub {α : Type} [Fintype α] (f g : α→ℝ) :
    synthesis_average (fun a=>f a-g a)=synthesis_average f-synthesis_average g := by
  simp only [synthesis_average,sum_sub_distrib,sub_div]

lemma average_smul {α : Type} [Fintype α] (c : ℝ) (f : α→ℝ) :
    synthesis_average (fun a=>c*f a)=c*synthesis_average f := by
  unfold synthesis_average
  rw [← mul_sum]
  ring

lemma average_mul_const {α : Type} [Fintype α] (f : α→ℝ) (c : ℝ) :
    synthesis_average (fun a=>f a*c)=synthesis_average f*c := by
  simpa only [mul_comm] using average_smul c f

lemma average_sum {α β : Type} [Fintype α] [Fintype β] (F : β→α→ℝ) :
    synthesis_average (fun a=>∑b,F b a)=∑b,synthesis_average (F b) := by
  unfold synthesis_average
  rw [sum_comm,sum_div]

lemma average_mono {α : Type} [Fintype α] (f g : α→ℝ) (h:∀a,f a ≤ g a) :
    synthesis_average f ≤ synthesis_average g :=
  div_le_div_of_nonneg_right (sum_le_sum (fun a _=>h a)) (Nat.cast_nonneg _)

variable {n m m₀ k : ℕ}

def visit (i : ℕ) : synthesis_Bits m₀ :=
  if hi:i<Fintype.card (synthesis_Bits m₀) then synthesis_order m₀ ⟨i,hi⟩ else fun _=>0

def backwardApply (C : synthesis_Circuit n m m₀ k) (r : ℝ) :
    ℕ→(synthesis_Oracle m₀→ℝ)→synthesis_Oracle m₀→ℝ
  | 0,h=>h
  | i+1,h=>backwardApply C r i (oneStepOp C r (visit i) h)

/-- Exact finite dynamic-programming semantics of the public adaptive path,
using its genuinely fresh fair seed bit at every visit. -/
theorem path_average_value (C : synthesis_Circuit n m m₀ k) (r : ℝ) (f : synthesis_Oracle m₀)
    (i : ℕ) (hi:i ≤ Fintype.card (synthesis_Bits m₀)) (h : synthesis_Oracle m₀→ℝ) :
    synthesis_average (fun coins:synthesis_Oracle m₀=>h (synthesis_resamplePath C r f coins i).1)=
      backwardApply C r i h f := by
  induction i generalizing h with
  | zero=>simp only [synthesis_resamplePath,backwardApply,average_const]
  | succ i ih=>
    have hi':i<Fintype.card (synthesis_Bits m₀) := by omega
    rw [average_next C r f i hi',ih (by omega)]
    simp only [backwardApply,visit,dif_pos hi']

/-- Averaging a real-valued observable after one update is the exact
orthogonal projection associated with the conditional bit flip. -/
def coordinateProjection (C : synthesis_Circuit n m m₀ k) (r : ℝ) (i : ℕ) :
    EuclideanSpace ℝ (synthesis_Oracle m₀)→EuclideanSpace ℝ (synthesis_Oracle m₀) :=
  pairProjection (lazyFlipEquiv C r (visit i))

lemma coordinateProjection_symm (C : synthesis_Circuit n m m₀ k) (r : ℝ) (i : ℕ)
    (u v : EuclideanSpace ℝ (synthesis_Oracle m₀)) :
    inner ℝ (coordinateProjection C r i u) v=inner ℝ u (coordinateProjection C r i v) :=
  pairProjection_symmetric _ (lazyFlip_involutive C r (visit i)) u v

lemma coordinateProjection_idempotent (C : synthesis_Circuit n m m₀ k) (r : ℝ) (i : ℕ)
    (v : EuclideanSpace ℝ (synthesis_Oracle m₀)) :
    coordinateProjection C r i (coordinateProjection C r i v)=coordinateProjection C r i v :=
  pairProjection_idempotent _ (lazyFlip_involutive C r (visit i)) v

lemma coordinateProjection_apply (C : synthesis_Circuit n m m₀ k) (r : ℝ) (i : ℕ)
    (v : EuclideanSpace ℝ (synthesis_Oracle m₀)) (f : synthesis_Oracle m₀) :
    coordinateProjection C r i v f=oneStepOp C r (visit i) v f := oneStepOp_projection C r _ v f

def backwardVector (C : synthesis_Circuit n m m₀ k) (r : ℝ) :
    ℕ→EuclideanSpace ℝ (synthesis_Oracle m₀)→EuclideanSpace ℝ (synthesis_Oracle m₀)
  | 0,v=>v
  | i+1,v=>backwardVector C r i (coordinateProjection C r i v)

lemma backwardVector_apply (C : synthesis_Circuit n m m₀ k) (r : ℝ) (i : ℕ)
    (v : EuclideanSpace ℝ (synthesis_Oracle m₀)) (f : synthesis_Oracle m₀) :
    backwardVector C r i v f=backwardApply C r i v f := by
  induction i generalizing v with
  | zero=>rfl
  | succ i ih=>
    rw [backwardVector,ih,backwardApply]
    congr 2
    funext g
    exact coordinateProjection_apply C r i v g

lemma backwardVector_inner_dual (C : synthesis_Circuit n m m₀ k) (r : ℝ) (i : ℕ)
    (u v : EuclideanSpace ℝ (synthesis_Oracle m₀)) :
    inner ℝ u (backwardVector C r i v)=inner ℝ (projectionPath (coordinateProjection C r) u i) v := by
  induction i generalizing v with
  | zero=>rfl
  | succ i ih=>
    rw [backwardVector,ih,← coordinateProjection_symm]
    rfl

end RandomOracleUnitarySynthesis.ResamplingProof

/- Module RandomOracleFiniteMeans -/

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace RandomOracleUnitarySynthesis.ResamplingProof
open Finset Classical
open scoped ENNReal

lemma mean_map {α β : Type} [Fintype α] [Fintype β] (p : PMF α) (f : α→β) (h : β→ℝ) :
    synthesis_mean (p.map f) h=synthesis_mean p (fun a=>h (f a)) := by
  have he:∀b:β,((p.map f) b).toReal=∑a:α,if b=f a then (p a).toReal else 0 := by
    intro b
    rw [PMF.map_apply,tsum_fintype,ENNReal.toReal_sum]
    · apply sum_congr rfl
      intro a ha
      split_ifs <;> simp
    · intro a ha
      split_ifs <;> simp [p.apply_ne_top]
  unfold synthesis_mean
  simp_rw [he,Finset.sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro a ha
  simp

lemma mean_uniform {α : Type} [Fintype α] [Nonempty α] (h : α→ℝ) :
    synthesis_mean (PMF.uniformOfFintype α) h=synthesis_average h := by
  unfold synthesis_mean synthesis_average
  simp only [PMF.uniformOfFintype_apply,ENNReal.toReal_inv,ENNReal.toReal_natCast]
  rw [← mul_sum]
  ring

lemma energy_eq_path {n m m₀ k : ℕ} (C : synthesis_Circuit n m m₀ k) (r : ℝ) :
    synthesis_energy C (synthesis_resample C r)=
      synthesis_average (fun f=>synthesis_average (fun coins:synthesis_Oracle m₀=>
        QAlgorithms.frobNorm (synthesis_A C f-
          synthesis_A C (synthesis_resamplePath C r f coins (Fintype.card (synthesis_Bits m₀))).1)^2)) := by
  unfold synthesis_energy synthesis_resample
  simp only [mean_map,mean_uniform]

end RandomOracleUnitarySynthesis.ResamplingProof

/- Module RandomOracleResamplingEntropy -/

set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
namespace RandomOracleUnitarySynthesis.ResamplingProof
open Matrix Finset Classical
variable {n m m₀ k : ℕ}

/-- Actual finite conditional law of the path, written as a normalized sum. -/
def pathMass (C : synthesis_Circuit n m m₀ k) (r : ℝ) (f : synthesis_Oracle m₀)
    (i : ℕ) (g : synthesis_Oracle m₀) : ℝ :=
  synthesis_average (fun coins:synthesis_Oracle m₀=>
    if (synthesis_resamplePath C r f coins i).1=g then 1 else 0)

lemma path_current_unvisited (C : synthesis_Circuit n m m₀ k) (r : ℝ)
    (f coins : synthesis_Oracle m₀) (i : ℕ) (j : Fin (Fintype.card (synthesis_Bits m₀)))
    (hij:i ≤ j.val) :
    (synthesis_resamplePath C r f coins i).1 (synthesis_order m₀ j)=f (synthesis_order m₀ j) := by
  induction i with
  | zero=>rfl
  | succ i ih=>
    have hi:i<Fintype.card (synthesis_Bits m₀) := by omega
    have hne:synthesis_order m₀ j≠synthesis_order m₀ ⟨i,hi⟩ := by
      intro hh
      have hv:j.val=i := congrArg Fin.val ((synthesis_order m₀).injective hh)
      omega
    simp only [synthesis_resamplePath,dif_pos hi]
    split_ifs <;> simp only [Function.update_of_ne hne,ih (by omega)]

lemma pathMass_zero (C : synthesis_Circuit n m m₀ k) (r : ℝ) (f g : synthesis_Oracle m₀)
    (i : ℕ) (j : Fin (Fintype.card (synthesis_Bits m₀))) (hij:i ≤ j.val)
    (hg:g (synthesis_order m₀ j)≠f (synthesis_order m₀ j)) : pathMass C r f i g=0 := by
  have hne:∀coins:synthesis_Oracle m₀,(synthesis_resamplePath C r f coins i).1≠g := by
    intro coins he
    have hh:=path_current_unvisited C r f coins i j hij
    rw [he] at hh
    exact hg hh
  simp only [pathMass,hne,if_false,average_const]

lemma pathMass_succ (C : synthesis_Circuit n m m₀ k) (r : ℝ) (f : synthesis_Oracle m₀)
    (i : ℕ) (hi:i<Fintype.card (synthesis_Bits m₀)) (g : synthesis_Oracle m₀) :
    pathMass C r f (i+1) g=oneStepOp C r (visit i) (pathMass C r f i) g := by
  have hv:visit i=synthesis_order m₀ ⟨i,hi⟩ := by simp only [visit,dif_pos hi]
  unfold pathMass
  rw [average_next C r f i hi (fun h:synthesis_Oracle m₀=>if h=g then 1 else 0),←hv]
  simp_rw [forced_pair_sum]
  have he:∀h:synthesis_Oracle m₀,lazyFlip C r (visit i) h=g ↔ h=lazyFlip C r (visit i) g := by
    intro h
    constructor
    · intro hh
      rw [←hh,lazyFlip_involutive C r (visit i) h]
    · intro hh
      rw [hh,lazyFlip_involutive C r (visit i) g]
  simp only [he,average_div,average_add]

lemma sum_oneStepOp (C : synthesis_Circuit n m m₀ k) (r : ℝ) (x : synthesis_Bits m₀)
    (a : synthesis_Oracle m₀→ℝ) : (∑f,oneStepOp C r x a f)=∑f,a f := by
  simp only [forced_pair_sum]
  rw [← sum_div,sum_add_distrib]
  have he:(∑f,a (lazyFlip C r x f))=∑f,a f := Equiv.sum_comp (lazyFlipEquiv C r x) a
  rw [he]
  ring

/-- A single Shannon summand, with the published zero-mass convention. -/
def entropyTerm (p : ℝ) : ℝ := -p*Real.logb 2 p

lemma entropyTerm_zero : entropyTerm 0=0 := by simp [entropyTerm]
lemma entropyTerm_one : entropyTerm 1=0 := by simp [entropyTerm]

lemma entropyTerm_half (p : ℝ) : entropyTerm (p/2)=entropyTerm p/2+p/2 := by
  by_cases hp:p=0
  · simp [hp,entropyTerm_zero]
  · unfold entropyTerm
    rw [Real.logb_div hp (by norm_num),Real.logb_self_eq_one (by norm_num : (1:ℝ)<2)]
    ring

lemma entropyTerm_half_pair (p q : ℝ) (h:p=0∨q=0) :
    entropyTerm ((p+q)/2)=(entropyTerm p+entropyTerm q)/2+(p+q)/2 := by
  rcases h with h|h
  · simp only [h,zero_add,entropyTerm_zero,entropyTerm_half]
  · simp only [h,add_zero,entropyTerm_zero,entropyTerm_half]

lemma entropy_oneStep (C : synthesis_Circuit n m m₀ k) (r : ℝ) (x : synthesis_Bits m₀)
    (p : synthesis_Oracle m₀→ℝ)
    (hp:∀f,p f=0∨p (synthesis_flip f x)=0) :
    FuchsVdGraaf.entropy (oneStepOp C r x p)=FuchsVdGraaf.entropy p+
      ∑f,if synthesis_resampleAllowed C r f x then p f else 0 := by
  have hpoint:∀f:synthesis_Oracle m₀,entropyTerm (oneStepOp C r x p f)=
      oneStepOp C r x (fun g=>entropyTerm (p g)) f+
      oneStepOp C r x (fun g=>if synthesis_resampleAllowed C r g x then p g else 0) f := by
    intro f
    simp only [forced_pair_sum]
    by_cases ha:synthesis_resampleAllowed C r f x
    · have hb:synthesis_resampleAllowed C r (synthesis_flip f x) x := (allowed_flip C r f x).mpr ha
      simp only [lazyFlip,if_pos ha,if_pos hb]
      exact entropyTerm_half_pair _ _ (hp f)
    · simp only [lazyFlip,if_neg ha,add_zero,zero_div]
      have he:(p f+p f)/2=p f := by ring
      rw [he]
      ring
  have hs:∀a:synthesis_Oracle m₀→ℝ,FuchsVdGraaf.entropy a=∑f,entropyTerm (a f) := by
    intro a
    unfold FuchsVdGraaf.entropy entropyTerm
    rw [← sum_neg_distrib]
    simp only [neg_mul]
  rw [hs,hs]
  simp_rw [hpoint]
  rw [sum_add_distrib,sum_oneStepOp,sum_oneStepOp]

lemma path_entropy_succ (C : synthesis_Circuit n m m₀ k) (r : ℝ) (f : synthesis_Oracle m₀)
    (i : ℕ) (hi:i<Fintype.card (synthesis_Bits m₀)) :
    FuchsVdGraaf.entropy (pathMass C r f (i+1))=FuchsVdGraaf.entropy (pathMass C r f i)+
      ∑g,if synthesis_resampleAllowed C r g (visit i) then pathMass C r f i g else 0 := by
  have hp:∀g:synthesis_Oracle m₀,pathMass C r f i g=0∨
      pathMass C r f i (synthesis_flip g (visit i))=0 := by
    intro g
    have hv:visit i=synthesis_order m₀ ⟨i,hi⟩ := by simp only [visit,dif_pos hi]
    by_cases hg:g (visit i)=f (visit i)
    · right
      apply pathMass_zero C r f _ i ⟨i,hi⟩ (le_refl _)
      rw [←hv]
      simp only [synthesis_flip,Function.update_self]
      rw [←hg]
      cases g (visit i) <;> decide
    · left
      exact pathMass_zero C r f g i ⟨i,hi⟩ (le_refl _) (by simpa only [hv] using hg)
  have hs: pathMass C r f (i+1)=oneStepOp C r (visit i) (pathMass C r f i) :=
    funext (pathMass_succ C r f i hi)
  rw [hs]
  exact entropy_oneStep C r (visit i) _ hp

end RandomOracleUnitarySynthesis.ResamplingProof

/- Module RandomOracleResamplingEntropyLaw -/

set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace RandomOracleUnitarySynthesis.ResamplingProof
open Finset Classical
variable {n m m₀ k : ℕ}

lemma uniform_map_real {α β : Type} [Fintype α] [Fintype β] [Nonempty α]
    (F : α→β) (b : β) : ((PMF.uniformOfFintype α).map F b).toReal=
      synthesis_average (fun a:α=>if F a=b then 1 else 0) := by
  calc
    _ = synthesis_mean ((PMF.uniformOfFintype α).map F) (fun c:β=>if c=b then 1 else 0) := by
      simp only [synthesis_mean,mul_ite,mul_one,mul_zero]
      simp
    _ = _ := by rw [mean_map,mean_uniform]

lemma pathMass_mean (C : synthesis_Circuit n m m₀ k) (r : ℝ) (f : synthesis_Oracle m₀)
    (i : ℕ) (a : synthesis_Oracle m₀→ℝ) :
    (∑g,pathMass C r f i g*a g)=synthesis_average (fun coins:synthesis_Oracle m₀=>
      a (synthesis_resamplePath C r f coins i).1) := by
  unfold pathMass synthesis_average
  simp only [div_mul_eq_mul_div,Finset.sum_mul,ite_mul,one_mul,zero_mul]
  rw [←sum_div,sum_comm]
  congr 1
  apply sum_congr rfl
  intro coins hc
  simp

lemma pathMass_initial_entropy (C : synthesis_Circuit n m m₀ k) (r : ℝ)
    (f : synthesis_Oracle m₀) : FuchsVdGraaf.entropy (pathMass C r f 0)=0 := by
  have he:∀g:synthesis_Oracle m₀,pathMass C r f 0 g=if f=g then 1 else 0 := by
    intro g
    unfold pathMass
    simp only [synthesis_resamplePath]
    exact average_const (α:=synthesis_Oracle m₀) (if f=g then 1 else 0)
  unfold FuchsVdGraaf.entropy
  simp only [he]
  have hz:∀g:synthesis_Oracle m₀,(if f=g then (1:ℝ) else 0)*Real.logb 2 (if f=g then 1 else 0)=0 := by
    intro g
    split_ifs <;> simp
  simp only [hz,sum_const_zero,neg_zero]

lemma average_path_entropy_succ (C : synthesis_Circuit n m m₀ k) (r : ℝ)
    (i : ℕ) (hi:i<Fintype.card (synthesis_Bits m₀)) :
    synthesis_average (fun f:synthesis_Oracle m₀=>FuchsVdGraaf.entropy (pathMass C r f (i+1)))=
      synthesis_average (fun f:synthesis_Oracle m₀=>FuchsVdGraaf.entropy (pathMass C r f i))+
      synthesis_average (fun f:synthesis_Oracle m₀=>if synthesis_resampleAllowed C r f (visit i) then 1 else 0) := by
  have he:∀f:synthesis_Oracle m₀,
      (∑g,if synthesis_resampleAllowed C r g (visit i) then pathMass C r f i g else 0)=
      synthesis_average (fun coins:synthesis_Oracle m₀=>
        if synthesis_resampleAllowed C r (synthesis_resamplePath C r f coins i).1 (visit i) then 1 else 0) := by
    intro f
    calc
      _ = ∑g,pathMass C r f i g*(if synthesis_resampleAllowed C r g (visit i) then 1 else 0) := by
        apply sum_congr rfl
        intro g hg
        split_ifs <;> simp only [mul_one,mul_zero]
      _ = _ := pathMass_mean C r f i (fun g=>if synthesis_resampleAllowed C r g (visit i) then 1 else 0)
  calc
    _ = synthesis_average (fun f:synthesis_Oracle m₀=>FuchsVdGraaf.entropy (pathMass C r f i)+
        ∑g,if synthesis_resampleAllowed C r g (visit i) then pathMass C r f i g else 0) :=
      congrArg synthesis_average (funext (fun f=>path_entropy_succ C r f i hi))
    _ = synthesis_average (fun f:synthesis_Oracle m₀=>FuchsVdGraaf.entropy (pathMass C r f i))+
        synthesis_average (fun f:synthesis_Oracle m₀=>
          ∑g,if synthesis_resampleAllowed C r g (visit i) then pathMass C r f i g else 0) := average_add _ _
    _ = _ := by
      congr 1
      calc
        _ = synthesis_average (fun f:synthesis_Oracle m₀=>synthesis_average (fun coins:synthesis_Oracle m₀=>
            if synthesis_resampleAllowed C r (synthesis_resamplePath C r f coins i).1 (visit i) then 1 else 0)) :=
          congrArg synthesis_average (funext he)
        _ = _ := average_path_current C r i (fun f:synthesis_Oracle m₀=>
          if synthesis_resampleAllowed C r f (visit i) then 1 else 0)

lemma average_path_entropy (C : synthesis_Circuit n m m₀ k) (r : ℝ)
    (T : ℕ) (hT:T ≤ Fintype.card (synthesis_Bits m₀)) :
    synthesis_average (fun f:synthesis_Oracle m₀=>FuchsVdGraaf.entropy (pathMass C r f T))=
      ∑i∈range T,synthesis_average (fun f:synthesis_Oracle m₀=>
        if synthesis_resampleAllowed C r f (visit i) then 1 else 0) := by
  induction T with
  | zero=>simp only [pathMass_initial_entropy,average_const,range_zero,sum_empty]
  | succ T ih=>
    rw [average_path_entropy_succ C r T (by omega),ih (by omega),sum_range_succ]

lemma resample_entropy_path (C : synthesis_Circuit n m m₀ k) (r : ℝ) :
    synthesis_conditionalEntropy (synthesis_resample C r)=
      synthesis_average (fun f:synthesis_Oracle m₀=>
        FuchsVdGraaf.entropy (pathMass C r f (Fintype.card (synthesis_Bits m₀)))) := by
  unfold synthesis_conditionalEntropy
  congr 1
  funext f
  congr 1
  funext g
  unfold synthesis_resample
  rw [PMF.map_comp]
  convert uniform_map_real (fun coins:synthesis_Oracle m₀=>
    (synthesis_resamplePath C r f coins (Fintype.card (synthesis_Bits m₀))).1) g using 1 <;> first | rfl | simp only [pathMass]
  apply congrArg synthesis_average
  funext coins
  split_ifs <;> rfl

/-- Exact entropy of the same actual finite resampler used in the energy proof. -/
theorem resample_entropy_eq (C : synthesis_Circuit n m m₀ k) (r : ℝ) :
    synthesis_conditionalEntropy (synthesis_resample C r)=
      ∑x:synthesis_Bits m₀,synthesis_average (fun f:synthesis_Oracle m₀=>
        if synthesis_resampleAllowed C r f x then 1 else 0) := by
  rw [resample_entropy_path,average_path_entropy C r _ (le_refl _),←Fin.sum_univ_eq_sum_range]
  have hv:∀i:Fin (Fintype.card (synthesis_Bits m₀)),visit i.val=synthesis_order m₀ i := by
    intro i
    simp only [visit,dif_pos i.isLt]
  simp_rw [hv]
  exact (synthesis_order m₀).sum_comp (fun x:synthesis_Bits m₀=>
    synthesis_average (fun f:synthesis_Oracle m₀=>if synthesis_resampleAllowed C r f x then 1 else 0))

end RandomOracleUnitarySynthesis.ResamplingProof

/- Module RandomOracleScalarEnergy -/

set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
namespace RandomOracleUnitarySynthesis.ResamplingProof
open Matrix Finset Classical
variable {n m m₀ k : ℕ}

def scalarEnergy (C : synthesis_Circuit n m m₀ k) (r : ℝ) (T : ℕ)
    (a : synthesis_Oracle m₀→ℝ) : ℝ :=
  synthesis_average (fun f=>synthesis_average (fun coins:synthesis_Oracle m₀=>
    (a (synthesis_resamplePath C r f coins T).1-a f)^2))

def scalarStepEnergy (C : synthesis_Circuit n m m₀ k) (r : ℝ) (i : ℕ)
    (a : synthesis_Oracle m₀→ℝ) : ℝ :=
  synthesis_average (fun f=>synthesis_average (fun coins:synthesis_Oracle m₀=>
    (a (synthesis_resamplePath C r f coins (i+1)).1-a (synthesis_resamplePath C r f coins i).1)^2))

lemma euclidean_inner {α : Type} [Fintype α] (u v : EuclideanSpace ℝ α) :
    inner ℝ u v=∑x,u x*v x := by
  simp only [PiLp.inner_apply,RCLike.inner_apply,starRingEnd_apply,star_trivial]
  apply sum_congr rfl
  intro x hx
  ring

lemma euclidean_norm_sq {α : Type} [Fintype α] (u : EuclideanSpace ℝ α) :
    ‖u‖^2=∑x,(u x)^2 := by rw [← real_inner_self_eq_norm_sq,euclidean_inner];simp only [pow_two]

lemma scalarEnergy_correlation (C : synthesis_Circuit n m m₀ k) (r : ℝ) (T : ℕ)
    (hT:T ≤ Fintype.card (synthesis_Bits m₀)) (a : synthesis_Oracle m₀→ℝ) :
    scalarEnergy C r T a=2*(synthesis_average (fun f=>a f^2)-
      synthesis_average (fun f=>a f*backwardApply C r T a f)) := by
  have he:∀f coins:synthesis_Oracle m₀,
      (a (synthesis_resamplePath C r f coins T).1-a f)^2=
      (a (synthesis_resamplePath C r f coins T).1)^2+(a f)^2-
        2*(a f*a (synthesis_resamplePath C r f coins T).1) := by intro f coins;ring
  unfold scalarEnergy
  simp_rw [he,average_sub,average_add,average_smul,average_const]
  rw [average_path_current C r T (fun f=>a f^2)]
  simp_rw [path_average_value C r _ T hT a]
  ring

lemma scalarEnergy_projection (C : synthesis_Circuit n m m₀ k) (r : ℝ) (T : ℕ)
    (hT:T ≤ Fintype.card (synthesis_Bits m₀)) (a : synthesis_Oracle m₀→ℝ) :
    scalarEnergy C r T a=
      2/(Fintype.card (synthesis_Oracle m₀):ℝ)*
        inner ℝ (WithLp.toLp 2 a) (WithLp.toLp 2 a-projectionPath (coordinateProjection C r) (WithLp.toLp 2 a) T) := by
  let v:EuclideanSpace ℝ (synthesis_Oracle m₀):=WithLp.toLp 2 a
  have hd:inner ℝ v (projectionPath (coordinateProjection C r) v T)=inner ℝ v (backwardVector C r T v) := by
    rw [backwardVector_inner_dual,real_inner_comm]
  have hi:inner ℝ v (v-projectionPath (coordinateProjection C r) v T)=
      (∑f,a f^2)-(∑f,a f*backwardApply C r T a f) := by
    rw [inner_sub_right,hd,euclidean_inner,euclidean_inner]
    simp only [v,PiLp.toLp_apply,backwardVector_apply,pow_two]
  rw [scalarEnergy_correlation C r T hT a]
  change _=2/(Fintype.card (synthesis_Oracle m₀):ℝ)*inner ℝ v (v-projectionPath (coordinateProjection C r) v T)
  rw [hi]
  unfold synthesis_average
  ring

def oneStepCost (C : synthesis_Circuit n m m₀ k) (r : ℝ) (x : synthesis_Bits m₀)
    (a : synthesis_Oracle m₀→ℝ) (f : synthesis_Oracle m₀) : ℝ :=
  ((a (step C r x f false)-a f)^2+(a (step C r x f true)-a f)^2)/2

lemma oneStepCost_projection (C : synthesis_Circuit n m m₀ k) (r : ℝ) (x : synthesis_Bits m₀)
    (a : synthesis_Oracle m₀→ℝ) (f : synthesis_Oracle m₀) :
    oneStepCost C r x a f=2*(a f-oneStepOp C r x a f)^2 := by
  unfold oneStepCost oneStepOp
  by_cases ha:synthesis_resampleAllowed C r f x
  · simp only [step,if_pos ha]
    have hf:Function.update f x (f x)=f := Function.update_eq_self x f
    cases hfx:f x
    · have h0:Function.update f x false=f := by simpa only [hfx] using hf
      rw [h0]
      ring
    · have h1:Function.update f x true=f := by simpa only [hfx] using hf
      rw [h1]
      ring
  · simp only [step,if_neg ha]
    ring

lemma scalarStepEnergy_cost (C : synthesis_Circuit n m m₀ k) (r : ℝ) (i : ℕ)
    (hi:i<Fintype.card (synthesis_Bits m₀)) (a : synthesis_Oracle m₀→ℝ) :
    scalarStepEnergy C r i a=synthesis_average (oneStepCost C r (visit i) a) := by
  have hpoint:∀f coins:synthesis_Oracle m₀,
      (synthesis_resamplePath C r f coins (i+1)).1=
      step C r (synthesis_order m₀ ⟨i,hi⟩) (synthesis_resamplePath C r f coins i).1
        (coins (synthesis_order m₀ ⟨i,hi⟩)) := by
    intro f coins
    simp only [synthesis_resamplePath,dif_pos hi,step]
    split_ifs <;> rfl
  unfold scalarStepEnergy
  simp_rw [hpoint]
  have he:∀f:synthesis_Oracle m₀,
      synthesis_average (fun coins:synthesis_Oracle m₀=>
        (a (step C r (synthesis_order m₀ ⟨i,hi⟩) (synthesis_resamplePath C r f coins i).1
          (coins (synthesis_order m₀ ⟨i,hi⟩)))-a (synthesis_resamplePath C r f coins i).1)^2)=
      synthesis_average (fun coins:synthesis_Oracle m₀=>
        oneStepCost C r (visit i) a (synthesis_resamplePath C r f coins i).1) := by
    intro f
    exact (average_fresh_bit C r f i hi (fun prev b=>
      (a (step C r (synthesis_order m₀ ⟨i,hi⟩) prev.1 b)-a prev.1)^2)).trans
      (by simp only [oneStepCost,visit,dif_pos hi])
  simp_rw [he]
  exact average_path_current C r i (oneStepCost C r (visit i) a)

lemma scalarStepEnergy_projection (C : synthesis_Circuit n m m₀ k) (r : ℝ) (i : ℕ)
    (hi:i<Fintype.card (synthesis_Bits m₀)) (a : synthesis_Oracle m₀→ℝ) :
    scalarStepEnergy C r i a=2/(Fintype.card (synthesis_Oracle m₀):ℝ)*
      ‖WithLp.toLp 2 a-coordinateProjection C r i (WithLp.toLp 2 a)‖^2 := by
  rw [scalarStepEnergy_cost C r i hi a]
  unfold synthesis_average
  simp_rw [oneStepCost_projection]
  rw [euclidean_norm_sq]
  simp only [PiLp.sub_apply,PiLp.toLp_apply,coordinateProjection_apply]
  rw [← mul_sum]
  ring

/-- The complete scalar version for the actual adaptive procedure.
The only normalization is uniform finite expectation. -/
theorem scalar_resampling_energy (C : synthesis_Circuit n m m₀ k) (r : ℝ) (T : ℕ)
    (hT:T ≤ Fintype.card (synthesis_Bits m₀)) (a : synthesis_Oracle m₀→ℝ) :
    scalarEnergy C r T a  ≤  2*(∑i∈range T,scalarStepEnergy C r i a) := by
  let v:EuclideanSpace ℝ (synthesis_Oracle m₀):=WithLp.toLp 2 a
  have hh:=projection_product_energy (coordinateProjection C r) v T
    (fun i hi=>coordinateProjection_symm C r i) (fun i hi=>coordinateProjection_idempotent C r i)
  have hfactor:0 ≤ 2/(Fintype.card (synthesis_Oracle m₀):ℝ) := by positivity
  have hm:=mul_le_mul_of_nonneg_left hh hfactor
  have he:(∑i∈range T,scalarStepEnergy C r i a)=
      2/(Fintype.card (synthesis_Oracle m₀):ℝ)*(∑i∈range T,‖v-coordinateProjection C r i v‖^2) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro i hi
    exact scalarStepEnergy_projection C r i (by have h:=mem_range.mp hi;omega) a
  rw [he,scalarEnergy_projection C r T hT a]
  dsimp only [v] at hm
  nlinarith

end RandomOracleUnitarySynthesis.ResamplingProof

/- Module RandomOracleInfluence -/

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace RandomOracleUnitarySynthesis.InfluenceProof
open Matrix Finset
open scoped ComplexConjugate

section Frobenius
variable {α β : Type} [Fintype α] [Fintype β]
open scoped Matrix.Norms.Frobenius in
lemma frob_sq_entries (A : Matrix α β ℂ) :
    QAlgorithms.frobNorm A^2=∑i,∑j,‖A i j‖^2 := by
  change ‖A‖^2=_
  rw [Matrix.frobenius_norm_def]
  simp only [Real.rpow_two]
  rw [← Real.sqrt_eq_rpow]
  exact Real.sq_sqrt (sum_nonneg (fun i _=>sum_nonneg (fun j _=>sq_nonneg _)))

lemma frob_sq_gram [DecidableEq β] (A : Matrix α β ℂ) :
    QAlgorithms.frobNorm A^2=(Aᴴ*A).trace.re := by
  rw [frob_sq_entries]
  simp only [Matrix.trace,Matrix.diag,Matrix.mul_apply,Matrix.conjTranspose_apply,Complex.re_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [← Complex.normSq_eq_norm_sq]
  simp [Complex.normSq_apply,Complex.mul_re,Complex.star_def]

lemma frob_sq_leftGram [DecidableEq α] [DecidableEq β] (A : Matrix α β ℂ) :
    QAlgorithms.frobNorm A^2=(A*Aᴴ).trace.re := by rw [frob_sq_gram,Matrix.trace_mul_comm]
end Frobenius

variable {n m m₀ k : ℕ}

lemma prefix_join (h:n ≤ m) (x : synthesis_Bits n) (a : synthesis_Bits (m-n)) :
    synthesis_prefix h (synthesis_join h x a)=x := by
  funext i
  simp [synthesis_prefix,synthesis_join,i.isLt]

lemma join_left_injective (h:n ≤ m) (a : synthesis_Bits (m-n)) :
    Function.Injective (fun x=>synthesis_join h x a) := by
  intro x y hh
  have hpre:=congrArg (synthesis_prefix h) hh
  simpa only [prefix_join] using hpre

lemma J_isometry (C : synthesis_Circuit n m m₀ k) : (synthesis_J C)ᴴ*synthesis_J C=1 := by
  have hinj:=join_left_injective C.system_le (fun _=>0)
  ext x y
  simp [synthesis_J,Matrix.mul_apply,Matrix.conjTranspose_apply,ite_mul,mul_ite,hinj.eq_iff,eq_comm,Matrix.one_apply]

lemma gate_unitary (C : synthesis_Circuit n m m₀ k) (i : ℕ) :
    synthesis_gate C i∈Matrix.unitaryGroup (synthesis_Bits m) ℂ := by
  unfold synthesis_gate
  split_ifs with hi
  · exact (C.gates ⟨i,hi⟩).property
  · exact one_mem _

lemma oracle_unitary (C : synthesis_Circuit n m m₀ k) (f : synthesis_Oracle m₀) :
    synthesis_oracle C f∈Matrix.unitaryGroup (synthesis_Bits m) ℂ := by
  apply Unitary.mem_iff.mpr
  constructor <;> ext x y <;> by_cases h:x=y
  all_goals simp [synthesis_oracle,Matrix.star_eq_conjTranspose,Matrix.diagonal_conjTranspose,
    Matrix.diagonal_mul_diagonal,Matrix.one_apply,Matrix.diagonal_apply,h]
  all_goals split_ifs <;> norm_num

lemma segment_unitary (C : synthesis_Circuit n m m₀ k) (f : synthesis_Oracle m₀) (a b : ℕ) :
    synthesis_segment C f a b∈Matrix.unitaryGroup (synthesis_Bits m) ℂ := by
  have hfold:∀(L:List ℕ) (W:synthesis_Mat m),W∈Matrix.unitaryGroup (synthesis_Bits m) ℂ→
      L.foldl (fun W t=>synthesis_gate C (a+t+1)*synthesis_oracle C f*W) W∈
        Matrix.unitaryGroup (synthesis_Bits m) ℂ := by
    intro L
    induction L with
    | nil => intro W hW;exact hW
    | cons t L ih =>
      intro W hW
      exact ih _ (mul_mem (mul_mem (gate_unitary C _) (oracle_unitary C f)) hW)
  exact hfold _ _ (gate_unitary C a)

lemma projector_columns (C : synthesis_Circuit n m m₀ k) (x : synthesis_Bits m₀)
    {α : Type} [Fintype α] (A : Matrix α (synthesis_Bits m) ℂ) (i : α) (j : synthesis_Bits m) :
    (A*synthesis_projector C x) i j=if synthesis_prefix C.oracle_le j=x then A i j else 0 := by
  simp [Matrix.mul_apply,synthesis_projector,ite_and,mul_ite]

lemma projector_rows (C : synthesis_Circuit n m m₀ k) (x : synthesis_Bits m₀)
    {α : Type} [Fintype α] (A : Matrix (synthesis_Bits m) α ℂ) (i : synthesis_Bits m) (j : α) :
    (synthesis_projector C x*A) i j=if synthesis_prefix C.oracle_le i=x then A i j else 0 := by
  simp [Matrix.mul_apply,synthesis_projector,ite_and,ite_mul]

lemma sum_projector_right_frob (C : synthesis_Circuit n m m₀ k)
    {α : Type} [Fintype α] (A : Matrix α (synthesis_Bits m) ℂ) :
    (∑x,QAlgorithms.frobNorm (A*synthesis_projector C x)^2)=QAlgorithms.frobNorm A^2 := by
  simp only [frob_sq_entries,projector_columns]
  rw [sum_comm]
  apply sum_congr rfl
  intro i hi
  rw [sum_comm]
  apply sum_congr rfl
  intro j hj
  rw [Finset.sum_eq_single (synthesis_prefix C.oracle_le j)]
  · simp
  · intro x hx hne
    simp [Ne.symm hne]
  · simp

lemma sum_projector_left_frob (C : synthesis_Circuit n m m₀ k)
    {α : Type} [Fintype α] (A : Matrix (synthesis_Bits m) α ℂ) :
    (∑x,QAlgorithms.frobNorm (synthesis_projector C x*A)^2)=QAlgorithms.frobNorm A^2 := by
  simp only [frob_sq_entries,projector_rows]
  rw [sum_comm]
  apply sum_congr rfl
  intro i hi
  rw [sum_comm]
  apply sum_congr rfl
  intro j hj
  rw [Finset.sum_eq_single (synthesis_prefix C.oracle_le i)]
  · simp
  · intro x hx hne
    simp [Ne.symm hne]
  · simp

lemma left_gram (C : synthesis_Circuit n m m₀ k) (f : synthesis_Oracle m₀) (j : Fin k) :
    synthesis_left C f j*(synthesis_left C f j)ᴴ=1 := by
  have hU:=segment_unitary C f (j.val+1) k
  have hh:(synthesis_segment C f (j.val+1) k)*(synthesis_segment C f (j.val+1) k)ᴴ=1 :=
    (Unitary.mem_iff.mp hU).2
  simp only [synthesis_left,Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose,Matrix.mul_assoc]
  rw [← Matrix.mul_assoc _ _ (synthesis_J C),hh,Matrix.one_mul,J_isometry]

lemma right_gram (C : synthesis_Circuit n m m₀ k) (f : synthesis_Oracle m₀) (j : Fin k) :
    (synthesis_right C f j)ᴴ*synthesis_right C f j=1 := by
  have hU:=segment_unitary C f 0 j.val
  have hh:(synthesis_segment C f 0 j.val)ᴴ*(synthesis_segment C f 0 j.val)=1 :=
    (Unitary.mem_iff.mp hU).1
  simp only [synthesis_right,Matrix.conjTranspose_mul,Matrix.mul_assoc]
  rw [← Matrix.mul_assoc _ _ (synthesis_J C),hh,Matrix.one_mul,J_isometry]

lemma trace_one_bits (n : ℕ) : ((1:synthesis_Mat n).trace).re=(2:ℝ)^n := by
  rw [Matrix.trace_one]
  simp only [Complex.natCast_re,Fintype.card_fun,Fintype.card_fin]
  norm_cast

/-- Exact public Lemma4.7, retaining the full computational basis and the
published circuit fold products and ancilla embedding. -/
theorem synthesis_total_influence (C : synthesis_Circuit n m m₀ k) (f : synthesis_Oracle m₀) :
    (∑x,synthesis_influence C f x)=2*(k:ℝ)*(2:ℝ)^n := by
  unfold synthesis_influence
  rw [sum_comm]
  simp only [sum_add_distrib,sum_projector_right_frob,sum_projector_left_frob]
  have he:∀j:Fin k,QAlgorithms.frobNorm (synthesis_left C f j)^2+
      QAlgorithms.frobNorm (synthesis_right C f j)^2=2*(2:ℝ)^n := by
    intro j
    rw [frob_sq_leftGram,frob_sq_gram,left_gram,right_gram,trace_one_bits]
    ring
  rw [← sum_add_distrib]
  simp only [he,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul]
  ring

end RandomOracleUnitarySynthesis.InfluenceProof

/- Module RandomOracleResamplingEnergy -/

set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
namespace RandomOracleUnitarySynthesis.ResamplingProof
open Matrix Finset Classical
open scoped ComplexConjugate

lemma frob_sq_sub_components {α β : Type} [Fintype α] [Fintype β] (A B : Matrix α β ℂ) :
    QAlgorithms.frobNorm (A-B)^2=
      ∑i,∑j,(((A i j).re-(B i j).re)^2+((A i j).im-(B i j).im)^2) := by
  rw [InfluenceProof.frob_sq_entries]
  apply sum_congr rfl
  intro i hi
  apply sum_congr rfl
  intro j hj
  rw [← Complex.normSq_eq_norm_sq]
  simp only [Matrix.sub_apply,Complex.normSq_apply,Complex.sub_re,Complex.sub_im]
  ring

lemma frob_sq_sub_comm {α β : Type} [Fintype α] [Fintype β] (A B : Matrix α β ℂ) :
    QAlgorithms.frobNorm (A-B)^2=QAlgorithms.frobNorm (B-A)^2 := by
  rw [frob_sq_sub_components,frob_sq_sub_components]
  apply sum_congr rfl
  intro i hi
  apply sum_congr rfl
  intro j hj
  ring

variable {n m m₀ k : ℕ}

lemma energy_components (C : synthesis_Circuit n m m₀ k) (r : ℝ) :
    synthesis_energy C (synthesis_resample C r)=
      ∑i,∑j,(scalarEnergy C r (Fintype.card (synthesis_Bits m₀)) (fun f=>(synthesis_A C f i j).re)+
        scalarEnergy C r (Fintype.card (synthesis_Bits m₀)) (fun f=>(synthesis_A C f i j).im)) := by
  rw [energy_eq_path]
  have he:∀f coins:synthesis_Oracle m₀,QAlgorithms.frobNorm (synthesis_A C f-
      synthesis_A C (synthesis_resamplePath C r f coins (Fintype.card (synthesis_Bits m₀))).1)^2=
      QAlgorithms.frobNorm (synthesis_A C (synthesis_resamplePath C r f coins
        (Fintype.card (synthesis_Bits m₀))).1-synthesis_A C f)^2 :=
    fun f coins=>frob_sq_sub_comm _ _
  simp_rw [he,frob_sq_sub_components,average_sum,average_add]
  rfl

lemma stepEnergy_components (C : synthesis_Circuit n m m₀ k) (r : ℝ) (t : ℕ) :
    synthesis_stepEnergy C r t=
      ∑i,∑j,(scalarStepEnergy C r t (fun f=>(synthesis_A C f i j).re)+
        scalarStepEnergy C r t (fun f=>(synthesis_A C f i j).im)) := by
  unfold synthesis_stepEnergy
  simp_rw [frob_sq_sub_components,average_sum,average_add]
  rfl

lemma triple_sum_comm {α β : Type} [Fintype α] [Fintype β] (T : ℕ) (F : α→β→ℕ→ℝ) :
    (∑i,∑j,∑t∈range T,F i j t)=∑t∈range T,∑i,∑j,F i j t := by
  calc
    _ = ∑i,∑t∈range T,∑j,F i j t := by
      apply sum_congr rfl
      intro i hi
      rw [sum_comm]
    _ = _ := sum_comm

/-- Exact public Lemma4.9. The scalar argument derives all conditional
averages, reversibility and stationarity for the published finite path. -/
theorem synthesis_resampling_energy (C : synthesis_Circuit n m m₀ k) (r : ℝ)
    (hr:0<r) (hr1:r ≤ 1) :
    synthesis_energy C (synthesis_resample C r)  ≤ 
      2*∑i:Fin (Fintype.card (synthesis_Bits m₀)),synthesis_stepEnergy C r i.val := by
  rw [energy_components,Fin.sum_univ_eq_sum_range]
  have he:∀i j,
      scalarEnergy C r (Fintype.card (synthesis_Bits m₀)) (fun f=>(synthesis_A C f i j).re)+
        scalarEnergy C r (Fintype.card (synthesis_Bits m₀)) (fun f=>(synthesis_A C f i j).im)  ≤ 
      2*∑t∈range (Fintype.card (synthesis_Bits m₀)),
        (scalarStepEnergy C r t (fun f=>(synthesis_A C f i j).re)+
          scalarStepEnergy C r t (fun f=>(synthesis_A C f i j).im)) := by
    intro i j
    have hRe:=scalar_resampling_energy C r (Fintype.card (synthesis_Bits m₀)) (le_refl _)
      (fun f=>(synthesis_A C f i j).re)
    have hIm:=scalar_resampling_energy C r (Fintype.card (synthesis_Bits m₀)) (le_refl _)
      (fun f=>(synthesis_A C f i j).im)
    rw [sum_add_distrib,mul_add]
    exact add_le_add hRe hIm
  have hs:=sum_le_sum (fun i (_:i∈(univ:Finset (synthesis_Bits n)))=>
    sum_le_sum (fun j (_:j∈(univ:Finset (synthesis_Bits n)))=>he i j))
  calc
    _  ≤  ∑i,∑j,2*∑t∈range (Fintype.card (synthesis_Bits m₀)),
      (scalarStepEnergy C r t (fun f=>(synthesis_A C f i j).re)+
        scalarStepEnergy C r t (fun f=>(synthesis_A C f i j).im)) := hs
    _ = 2*∑t∈range (Fintype.card (synthesis_Bits m₀)),synthesis_stepEnergy C r t := by
      simp_rw [← mul_sum]
      congr 1
      rw [triple_sum_comm]
      simp only [stepEnergy_components]

end RandomOracleUnitarySynthesis.ResamplingProof

/- Module RandomOracleSegments -/

set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
namespace RandomOracleUnitarySynthesis.InfluenceProof
open Matrix Finset
open scoped ComplexConjugate
variable {n m m₀ k : ℕ}

lemma segment_self (C : synthesis_Circuit n m m₀ k) (f : synthesis_Oracle m₀) (a : ℕ) :
    synthesis_segment C f a a=synthesis_gate C a := by simp [synthesis_segment]

lemma segment_succ (C : synthesis_Circuit n m m₀ k) (f : synthesis_Oracle m₀) (a b : ℕ)
    (hab:a ≤ b) : synthesis_segment C f a (b+1)=
      synthesis_gate C (b+1)*synthesis_oracle C f*synthesis_segment C f a b := by
  unfold synthesis_segment
  have hd:b+1-a=(b-a)+1 := by omega
  rw [hd,List.range_succ,List.foldl_append]
  simp only [List.foldl_cons,List.foldl_nil]
  have hi:a+(b-a)+1=b+1 := by omega
  rw [hi]

/-- Literal circuit-fold product difference; each summand uses the left
segment from f and the right segment from g, with no unproved hybrid rule. -/
theorem segment_difference (C : synthesis_Circuit n m m₀ k) (f g : synthesis_Oracle m₀)
    (b : ℕ) :
    synthesis_segment C g 0 b-synthesis_segment C f 0 b=
      ∑j∈Finset.range b,synthesis_segment C f (j+1) b*
        (synthesis_oracle C g-synthesis_oracle C f)*synthesis_segment C g 0 j := by
  induction b with
  | zero => simp [synthesis_segment]
  | succ b ih =>
    rw [segment_succ C g 0 b (Nat.zero_le b),segment_succ C f 0 b (Nat.zero_le b),sum_range_succ]
    have he:synthesis_gate C (b+1)*synthesis_oracle C g*synthesis_segment C g 0 b-
        synthesis_gate C (b+1)*synthesis_oracle C f*synthesis_segment C f 0 b=
        synthesis_gate C (b+1)*synthesis_oracle C f*
          (synthesis_segment C g 0 b-synthesis_segment C f 0 b)+
        synthesis_gate C (b+1)*(synthesis_oracle C g-synthesis_oracle C f)*synthesis_segment C g 0 b := by
      noncomm_ring
    rw [he,ih,Matrix.mul_sum,segment_self]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    rw [segment_succ C f (j+1) b (by have hh:=Finset.mem_range.mp hj;omega)]
    simp only [Matrix.mul_assoc]

theorem A_difference (C : synthesis_Circuit n m m₀ k) (f g : synthesis_Oracle m₀) :
    synthesis_A C g-synthesis_A C f=
      ∑j:Fin k,synthesis_left C f j*(synthesis_oracle C g-synthesis_oracle C f)*synthesis_right C g j := by
  unfold synthesis_A synthesis_W
  rw [← Matrix.sub_mul,← Matrix.mul_sub,segment_difference,Matrix.mul_sum,Matrix.sum_mul]
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [synthesis_left,synthesis_right,Matrix.mul_assoc]

lemma projector_idempotent (C : synthesis_Circuit n m m₀ k) (x : synthesis_Bits m₀) :
    synthesis_projector C x*synthesis_projector C x=synthesis_projector C x := by
  ext y z
  rw [projector_rows]
  by_cases h:synthesis_prefix C.oracle_le y=x <;> simp [synthesis_projector,h]

lemma oracle_flip_difference (C : synthesis_Circuit n m m₀ k) (f : synthesis_Oracle m₀)
    (x : synthesis_Bits m₀) :
    synthesis_oracle C (synthesis_flip f x)-synthesis_oracle C f=
      (if f x then (2:ℂ) else -2) • synthesis_projector C x := by
  ext y z
  by_cases hyz:y=z
  · subst z
    by_cases hx:synthesis_prefix C.oracle_le y=x
    · simp [synthesis_oracle,synthesis_flip,synthesis_projector,hx]
      cases f x <;> norm_num
    · simp [synthesis_oracle,synthesis_flip,synthesis_projector,hx,Ne.symm hx]
  · simp [synthesis_oracle,synthesis_projector,Matrix.diagonal_apply,hyz]

theorem A_flip_difference (C : synthesis_Circuit n m m₀ k) (f : synthesis_Oracle m₀)
    (x : synthesis_Bits m₀) :
    synthesis_A C (synthesis_flip f x)-synthesis_A C f=
      (if f x then (2:ℂ) else -2) •
        ∑j:Fin k,(synthesis_left C f j*synthesis_projector C x)*
          (synthesis_projector C x*synthesis_right C (synthesis_flip f x) j) := by
  rw [A_difference,oracle_flip_difference,Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Matrix.mul_smul,Matrix.smul_mul]
  congr 1
  simp only [Matrix.mul_assoc,← Matrix.mul_assoc (synthesis_projector C x) (synthesis_projector C x),
    projector_idempotent]

end RandomOracleUnitarySynthesis.InfluenceProof

/- Module RandomOraclePerturbation -/

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace RandomOracleUnitarySynthesis.InfluenceProof
open Matrix Finset
open scoped ComplexConjugate

section Frobenius
variable {ι α β γ : Type} [Fintype ι] [Fintype α] [Fintype β] [Fintype γ]
open scoped Matrix.Norms.Frobenius in
lemma frob_nonneg (A : Matrix α β ℂ) : 0 ≤ QAlgorithms.frobNorm A := norm_nonneg _

open scoped Matrix.Norms.Frobenius in
lemma frob_smul (c : ℂ) (A : Matrix α β ℂ) :
    QAlgorithms.frobNorm (c • A)=‖c‖*QAlgorithms.frobNorm A := norm_smul _ _

open scoped Matrix.Norms.Frobenius in
/-- Finite Schatten--Cauchy--Schwarz, equivalently the horizontal/vertical
block-factor argument in the original proof. There is no extra k factor. -/
theorem frob_sum_mul_sq_le (A : ι→Matrix α β ℂ) (B : ι→Matrix β γ ℂ) :
    QAlgorithms.frobNorm (∑j,A j*B j)^2  ≤ 
      (∑j,QAlgorithms.frobNorm (A j)^2)*(∑j,QAlgorithms.frobNorm (B j)^2) := by
  have htriangle:QAlgorithms.frobNorm (∑j,A j*B j)  ≤  ∑j,QAlgorithms.frobNorm (A j*B j) :=
    norm_sum_le _ _
  have hmul:∀j,QAlgorithms.frobNorm (A j*B j)  ≤  QAlgorithms.frobNorm (A j)*QAlgorithms.frobNorm (B j) :=
    fun j=>Matrix.frobenius_norm_mul _ _
  have hcs:=Real.sum_mul_le_sqrt_mul_sqrt (univ:Finset ι)
    (fun j=>QAlgorithms.frobNorm (A j)) (fun j=>QAlgorithms.frobNorm (B j))
  have hh:=htriangle.trans ((sum_le_sum (fun j _=>hmul j)).trans hcs)
  have hA:0 ≤ ∑j,QAlgorithms.frobNorm (A j)^2 := sum_nonneg (fun j _=>sq_nonneg _)
  have hB:0 ≤ ∑j,QAlgorithms.frobNorm (B j)^2 := sum_nonneg (fun j _=>sq_nonneg _)
  have hs:=pow_le_pow_left₀ (frob_nonneg _) hh 2
  rw [mul_pow,Real.sq_sqrt hA,Real.sq_sqrt hB] at hs
  exact hs
end Frobenius

variable {n m m₀ k : ℕ}

lemma influence_nonneg (C : synthesis_Circuit n m m₀ k) (f : synthesis_Oracle m₀) (x : synthesis_Bits m₀) :
    0 ≤ synthesis_influence C f x := by
  exact sum_nonneg (fun j _=>add_nonneg (sq_nonneg _) (sq_nonneg _))

/-- Exact public Lemma4.8 for the full oracle and the compressed block. -/
theorem synthesis_one_bit_perturbation (C : synthesis_Circuit n m m₀ k) (f : synthesis_Oracle m₀)
    (x : synthesis_Bits m₀) :
    QAlgorithms.frobNorm (synthesis_A C (synthesis_flip f x)-synthesis_A C f)^2  ≤ 
      4*synthesis_influence C f x*synthesis_influence C (synthesis_flip f x) x := by
  have hA:(∑j:Fin k,QAlgorithms.frobNorm (synthesis_left C f j*synthesis_projector C x)^2)  ≤ 
      synthesis_influence C f x := sum_le_sum (fun j _=>le_add_of_nonneg_right (sq_nonneg _))
  have hB:(∑j:Fin k,QAlgorithms.frobNorm (synthesis_projector C x*synthesis_right C (synthesis_flip f x) j)^2)  ≤ 
      synthesis_influence C (synthesis_flip f x) x := sum_le_sum (fun j _=>
        le_add_of_nonneg_left (sq_nonneg _))
  have hh:=frob_sum_mul_sq_le
    (fun j:Fin k=>synthesis_left C f j*synthesis_projector C x)
    (fun j:Fin k=>synthesis_projector C x*synthesis_right C (synthesis_flip f x) j)
  have hb0:0 ≤ ∑j:Fin k,QAlgorithms.frobNorm
      (synthesis_projector C x*synthesis_right C (synthesis_flip f x) j)^2 := sum_nonneg (fun j _=>sq_nonneg _)
  have hp:=mul_le_mul hA hB hb0 (influence_nonneg C f x)
  rw [A_flip_difference,frob_smul,mul_pow]
  have hc:‖(if f x then (2:ℂ) else -2)‖^2=4 := by cases f x <;> norm_num
  rw [hc]
  nlinarith [hh.trans hp]

end RandomOracleUnitarySynthesis.InfluenceProof

/- Module RandomOracleResamplingEnergyBound -/

set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
namespace RandomOracleUnitarySynthesis.ResamplingProof
open Matrix Finset Classical
open scoped ComplexConjugate
variable {n m m₀ k : ℕ}

lemma threshold_nonneg (k : ℕ) (r : ℝ) : 0 ≤ synthesis_threshold k r := by
  unfold synthesis_threshold
  split_ifs <;> positivity

lemma oneStepCost_flip (C : synthesis_Circuit n m m₀ k) (r : ℝ) (x : synthesis_Bits m₀)
    (a : synthesis_Oracle m₀→ℝ) (f : synthesis_Oracle m₀) :
    oneStepCost C r x a f=if synthesis_resampleAllowed C r f x then
      (a (synthesis_flip f x)-a f)^2/2 else 0 := by
  rw [oneStepCost_projection,forced_pair_sum]
  by_cases ha:synthesis_resampleAllowed C r f x
  · simp only [lazyFlip,if_pos ha]
    ring
  · simp only [lazyFlip,if_neg ha]
    ring

lemma stepEnergy_allowed (C : synthesis_Circuit n m m₀ k) (r : ℝ) (i : ℕ)
    (hi:i<Fintype.card (synthesis_Bits m₀)) :
    synthesis_stepEnergy C r i=synthesis_average (fun f:synthesis_Oracle m₀=>
      if synthesis_resampleAllowed C r f (visit i) then
        QAlgorithms.frobNorm (synthesis_A C (synthesis_flip f (visit i))-synthesis_A C f)^2/2 else 0) := by
  have hp : ∀ f : synthesis_Oracle m₀,
      (∑a,∑b,(oneStepCost C r (visit i) (fun g=>(synthesis_A C g a b).re) f+
        oneStepCost C r (visit i) (fun g=>(synthesis_A C g a b).im) f))=
      if synthesis_resampleAllowed C r f (visit i) then
        QAlgorithms.frobNorm (synthesis_A C (synthesis_flip f (visit i))-synthesis_A C f)^2/2 else 0 := by
    intro f
    simp_rw [oneStepCost_flip]
    by_cases ha:synthesis_resampleAllowed C r f (visit i)
    · simp only [if_pos ha]
      rw [frob_sq_sub_components]
      simp only [sum_div,add_div]
    · simp only [if_neg ha,zero_add,sum_const_zero]
  rw [stepEnergy_components]
  simp_rw [scalarStepEnergy_cost C r i hi]
  calc
    _ = synthesis_average (fun f:synthesis_Oracle m₀=>
        ∑a,∑b,(oneStepCost C r (visit i) (fun g=>(synthesis_A C g a b).re) f+
          oneStepCost C r (visit i) (fun g=>(synthesis_A C g a b).im) f)) := by
      simp only [average_sum,average_add]
    _ = _ := congrArg synthesis_average (funext hp)

lemma allowed_influences (C : synthesis_Circuit n m m₀ k) (r : ℝ) (f : synthesis_Oracle m₀)
    (x : synthesis_Bits m₀) (ha:synthesis_resampleAllowed C r f x) :
    synthesis_influence C f x ≤ synthesis_threshold k r ∧
      synthesis_influence C (synthesis_flip f x) x ≤ synthesis_threshold k r := by
  have hf:Function.update f x (f x)=f := Function.update_eq_self x f
  cases hfx:f x
  · have h0:Function.update f x false=f := by simpa only [hfx] using hf
    exact ⟨by simpa only [h0] using ha.1,by simpa only [synthesis_flip,hfx,Bool.not_false] using ha.2⟩
  · have h1:Function.update f x true=f := by simpa only [hfx] using hf
    exact ⟨by simpa only [h1] using ha.2,by simpa only [synthesis_flip,hfx,Bool.not_true] using ha.1⟩

lemma stepEnergy_influence (C : synthesis_Circuit n m m₀ k) (r : ℝ) (i : ℕ)
    (hi:i<Fintype.card (synthesis_Bits m₀)) :
    synthesis_stepEnergy C r i ≤ 2*synthesis_threshold k r*
      synthesis_average (fun f:synthesis_Oracle m₀=>synthesis_influence C f (visit i)) := by
  rw [stepEnergy_allowed C r i hi]
  have hp:∀f:synthesis_Oracle m₀,
      (if synthesis_resampleAllowed C r f (visit i) then
        QAlgorithms.frobNorm (synthesis_A C (synthesis_flip f (visit i))-synthesis_A C f)^2/2 else 0) ≤ 
      2*synthesis_threshold k r*synthesis_influence C (synthesis_flip f (visit i)) (visit i) := by
    intro f
    have hw:=InfluenceProof.influence_nonneg C (synthesis_flip f (visit i)) (visit i)
    by_cases ha:synthesis_resampleAllowed C r f (visit i)
    · rw [if_pos ha]
      have hh:=InfluenceProof.synthesis_one_bit_perturbation C f (visit i)
      have hf:=(allowed_influences C r f (visit i) ha).1
      nlinarith [mul_le_mul_of_nonneg_right hf hw]
    · rw [if_neg ha]
      exact mul_nonneg (mul_nonneg (by norm_num) (threshold_nonneg k r)) hw
  have hh:=average_mono _ _ hp
  rw [average_smul] at hh
  let e:Equiv.Perm (synthesis_Oracle m₀):=(flip_involutive (visit i)).toPerm
  have he:synthesis_average (fun f:synthesis_Oracle m₀=>synthesis_influence C (synthesis_flip f (visit i)) (visit i))=
      synthesis_average (fun f:synthesis_Oracle m₀=>synthesis_influence C f (visit i)) := by
    have he':=average_comp e (fun f=>synthesis_influence C f (visit i))
    change synthesis_average (fun f:synthesis_Oracle m₀=>
      synthesis_influence C (synthesis_flip f (visit i)) (visit i))=_ at he'
    exact he' 
  rwa [he] at hh

theorem sum_stepEnergy_bound (C : synthesis_Circuit n m m₀ k) (r : ℝ) :
    (∑i:Fin (Fintype.card (synthesis_Bits m₀)),synthesis_stepEnergy C r i.val)  ≤ 
      4*synthesis_threshold k r*(k:ℝ)*(2:ℝ)^n := by
  have hh:=sum_le_sum (fun i (_:i∈(univ:Finset (Fin (Fintype.card (synthesis_Bits m₀)))))=>
    stepEnergy_influence C r i.val i.isLt)
  have hv:∀i:Fin (Fintype.card (synthesis_Bits m₀)),visit i.val=synthesis_order m₀ i := by
    intro i
    simp only [visit,dif_pos i.isLt]
  simp_rw [hv] at hh
  rw [← mul_sum,← average_sum] at hh
  have htot:∀f:synthesis_Oracle m₀,(∑i:Fin (Fintype.card (synthesis_Bits m₀)),
      synthesis_influence C f (synthesis_order m₀ i))=2*(k:ℝ)*(2:ℝ)^n := by
    intro f
    rw [(synthesis_order m₀).sum_comp,InfluenceProof.synthesis_total_influence]
  simp only [htot,average_const] at hh
  convert hh using 1 <;> first | rfl | ring

/-- Energy half of Theorem4.5, for the same actual resampler to be used
in the entropy half. The k=0 threshold is handled without division by zero. -/
theorem resample_energy_bound (C : synthesis_Circuit n m m₀ k) (r : ℝ) (hr:0<r) (hr1:r ≤ 1) :
    synthesis_energy C (synthesis_resample C r)  ≤  2*(2:ℝ)^n*r^2 := by
  have hE:=synthesis_resampling_energy C r hr hr1
  have hS:=sum_stepEnergy_bound C r
  have hτ:8*synthesis_threshold k r*(k:ℝ) ≤ r^2 := by
    by_cases hk:k=0
    · simp only [hk,Nat.cast_zero,mul_zero]
      exact sq_nonneg r
    · have hkR:(k:ℝ)≠0 := by exact_mod_cast hk
      unfold synthesis_threshold
      rw [if_neg hk]
      field_simp
      ring_nf
      exact le_rfl
  have hN:0 ≤ (2:ℝ)^n := pow_nonneg (by norm_num) n
  have hmul:=mul_le_mul_of_nonneg_right hτ hN
  nlinarith [mul_nonneg hN (sq_nonneg r)]

end RandomOracleUnitarySynthesis.ResamplingProof

/- Module RandomOracleResamplingEntropyBound -/

set_option autoImplicit false
set_option maxHeartbeats 300000
noncomputable section
namespace RandomOracleUnitarySynthesis.ResamplingProof
open Finset Classical
variable {n m m₀ k : ℕ}

lemma allowed_iff_influences (C : synthesis_Circuit n m m₀ k) (r : ℝ)
    (f : synthesis_Oracle m₀) (x : synthesis_Bits m₀) :
    synthesis_resampleAllowed C r f x ↔ synthesis_influence C f x ≤ synthesis_threshold k r ∧
      synthesis_influence C (synthesis_flip f x) x ≤ synthesis_threshold k r := by
  constructor
  · exact allowed_influences C r f x
  · intro ha
    have hf:Function.update f x (f x)=f := Function.update_eq_self x f
    cases hfx:f x
    · have h0:Function.update f x false=f := by simpa only [hfx] using hf
      refine ⟨?_,?_⟩
      · simpa only [h0] using ha.1
      · simpa only [synthesis_flip,hfx,Bool.not_false] using ha.2
    · have h1:Function.update f x true=f := by simpa only [hfx] using hf
      refine ⟨?_,?_⟩
      · simpa only [synthesis_flip,hfx,Bool.not_true] using ha.2
      · simpa only [h1] using ha.1

lemma rejection_influence (C : synthesis_Circuit n m m₀ k) (r : ℝ)
    (f : synthesis_Oracle m₀) (x : synthesis_Bits m₀) :
    synthesis_threshold k r*(1-(if synthesis_resampleAllowed C r f x then 1 else 0)) ≤
      synthesis_influence C f x+synthesis_influence C (synthesis_flip f x) x := by
  have h0:=InfluenceProof.influence_nonneg C f x
  have h1:=InfluenceProof.influence_nonneg C (synthesis_flip f x) x
  by_cases ha:synthesis_resampleAllowed C r f x
  · simp only [if_pos ha,sub_self,mul_zero]
    exact add_nonneg h0 h1
  · simp only [if_neg ha,sub_zero,mul_one]
    rw [allowed_iff_influences] at ha
    by_cases hf:synthesis_influence C f x ≤ synthesis_threshold k r
    · have hg:¬synthesis_influence C (synthesis_flip f x) x ≤ synthesis_threshold k r := fun hh=>ha ⟨hf,hh⟩
      linarith
    · linarith

lemma average_flip_influence (C : synthesis_Circuit n m m₀ k) (x : synthesis_Bits m₀) :
    synthesis_average (fun f:synthesis_Oracle m₀=>synthesis_influence C (synthesis_flip f x) x)=
      synthesis_average (fun f:synthesis_Oracle m₀=>synthesis_influence C f x) := by
  let e:Equiv.Perm (synthesis_Oracle m₀):=(flip_involutive x).toPerm
  have he:=average_comp e (fun f:synthesis_Oracle m₀=>synthesis_influence C f x)
  change synthesis_average (fun f:synthesis_Oracle m₀=>synthesis_influence C (synthesis_flip f x) x)=_ at he
  exact he

lemma threshold_entropy_deficit (C : synthesis_Circuit n m m₀ k) (r : ℝ) :
    synthesis_threshold k r*((2:ℝ)^m₀-synthesis_conditionalEntropy (synthesis_resample C r)) ≤
      4*(k:ℝ)*(2:ℝ)^n := by
  have hx:∀x:synthesis_Bits m₀,synthesis_threshold k r*
      (1-synthesis_average (fun f:synthesis_Oracle m₀=>if synthesis_resampleAllowed C r f x then 1 else 0)) ≤
      2*synthesis_average (fun f:synthesis_Oracle m₀=>synthesis_influence C f x) := by
    intro x
    have hh:=average_mono _ _ (fun f:synthesis_Oracle m₀=>rejection_influence C r f x)
    rw [average_smul,average_sub,average_const,average_add,average_flip_influence] at hh
    linarith
  have hh:=sum_le_sum (fun x (_:x∈(univ:Finset (synthesis_Bits m₀)))=>hx x)
  rw [←mul_sum,sum_sub_distrib,←mul_sum] at hh
  have htot:∀f:synthesis_Oracle m₀,(∑x:synthesis_Bits m₀,synthesis_influence C f x)=2*(k:ℝ)*(2:ℝ)^n :=
    fun f=>InfluenceProof.synthesis_total_influence C f
  have hw:(∑x:synthesis_Bits m₀,synthesis_average (fun f:synthesis_Oracle m₀=>
      synthesis_influence C f x))=2*(k:ℝ)*(2:ℝ)^n := by
    rw [←average_sum]
    simp only [htot,average_const]
  rw [hw] at hh
  simp only [sum_const,card_univ,nsmul_eq_mul,mul_one] at hh
  have hc:(Fintype.card (synthesis_Bits m₀):ℝ)=(2:ℝ)^m₀ := by
    simp [synthesis_Bits,DirectFidelity.State.Q,Fintype.card_fun]
  rw [hc,←resample_entropy_eq] at hh
  convert hh using 1 <;> first | rfl | ring

theorem resample_entropy_bound (C : synthesis_Circuit n m m₀ k) (r : ℝ) (hr:0<r) :
    (2:ℝ)^m₀-32*(k:ℝ)^2*(2:ℝ)^n/r^2 ≤
      synthesis_conditionalEntropy (synthesis_resample C r) := by
  by_cases hk:k=0
  · subst k
    have ha:∀x:synthesis_Bits m₀,∀f:synthesis_Oracle m₀,synthesis_resampleAllowed C r f x := by
      intro x f
      simp [synthesis_resampleAllowed,synthesis_influence,synthesis_threshold]
    rw [resample_entropy_eq]
    simp [ha,average_const,synthesis_Bits,DirectFidelity.State.Q]
  · have hkR:0<(k:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hk
    have hτ:0<synthesis_threshold k r := by
      simp only [synthesis_threshold,if_neg hk]
      positivity
    have hd: (2:ℝ)^m₀-synthesis_conditionalEntropy (synthesis_resample C r) ≤
        4*(k:ℝ)*(2:ℝ)^n/synthesis_threshold k r := by
      apply (le_div_iff₀ hτ).mpr
      simpa only [mul_comm] using threshold_entropy_deficit C r
    have he:4*(k:ℝ)*(2:ℝ)^n/synthesis_threshold k r=32*(k:ℝ)^2*(2:ℝ)^n/r^2 := by
      simp only [synthesis_threshold,if_neg hk]
      field_simp [ne_of_gt hr,ne_of_gt hkR]
      <;> ring
    rw [he] at hd
    linarith

end RandomOracleUnitarySynthesis.ResamplingProof

/- Module RandomOracleEntropyResamplingMain -/

set_option autoImplicit false
noncomputable section
namespace RandomOracleUnitarySynthesis

/-- The exact public Theorem 4.5: both conclusions use the concrete
published path and the same finite PMF kernel, including zero queries. -/
theorem synthesis_entropy_resampling {n m m₀ k : ℕ}
    (C : synthesis_Circuit n m m₀ k) (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1) :
    ∃ K : synthesis_Resampler m₀,
      (2 : ℝ)^m₀ - 32 * (k : ℝ)^2 * (2 : ℝ)^n / r^2 ≤ synthesis_conditionalEntropy K ∧
      synthesis_energy C K ≤ 2 * (2 : ℝ)^n * r^2 := by
  exact ⟨synthesis_resample C r,ResamplingProof.resample_entropy_bound C r hr,
    ResamplingProof.resample_energy_bound C r hr hr1⟩

end RandomOracleUnitarySynthesis

open RandomOracleUnitarySynthesis

theorem solution {n m m₀ k : ℕ}
    (C : synthesis_Circuit n m m₀ k) (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1) :
    ∃ K : synthesis_Resampler m₀,
      (2 : ℝ)^m₀ - 32 * (k : ℝ)^2 * (2 : ℝ)^n / r^2 ≤ synthesis_conditionalEntropy K ∧
      synthesis_energy C K ≤ 2 * (2 : ℝ)^n * r^2 :=
  RandomOracleUnitarySynthesis.synthesis_entropy_resampling C r hr hr1
